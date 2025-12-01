package cs320

object Implementation extends Template {

  def typeCheck(e: Typed.Expr): Typed.Type = T.typeCheck(e)

  def interp(e: Untyped.Expr): Untyped.Value = U.interp(e)._1

  object T {
    import Typed._

    type TypeEnv = Map[String, Type]

    def checkIntOp(left: Expr, right: Expr, env: TypeEnv, resType: Type): Type = {
      val lt = typeCheck(left, env)
      val rt = typeCheck(right, env)
      (lt, rt) match {
        case (IntT, IntT) => resType
        case _ => error("type error in integer operation")
      }
    }

    def typeCheck(expr: Expr): Type = typeCheck(expr, Map())
    def typeCheck(expr: Expr, env: TypeEnv): Type = expr match {
      case Id(name, targs) => {
        
        env.getOrElse(name, error("free identifier"))
      }
      case IntE(value) => IntT
      case BooleanE(value) => BooleanT
      case UnitE => UnitT
      case Add(left, right) => checkIntOp(left, right, env, IntT)
      case Mul(left, right) => checkIntOp(left, right, env, IntT)
      case Div(left, right) => checkIntOp(left, right, env, IntT)
      case Mod(left, right) => checkIntOp(left, right, env, IntT)
      case Eq(left, right) => checkIntOp(left, right, env, BooleanT)
      case Lt(left, right) => checkIntOp(left, right, env, BooleanT)
      case Sequence(left, right) => {
        typeCheck(left, env)
        typeCheck(right, env)
      }
      case If(cond, texpr, fexpr) => {
        val ct = typeCheck(cond, env)
        val tt = typeCheck(texpr, env)
        val ft = typeCheck(fexpr, env)
        ct match {
          case BooleanT => {
            if (tt == ft) tt
            else error("branches of if have different types")
          }
          case _ => error("condition of if is not a boolean")
        }
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
        val newEnv = env ++ defs.flatMap{
          case Lazy(name, expr) => {
            val addr = malloc(sto)
            List(name -> addr)
          }
          case RecFun(name, params, expr) => {
            val addr = malloc(sto)
            List(name -> addr)
          }
          case TypeDef(variants) => variants.map{
            case Variant(vname, _) => (vname -> malloc(sto))
          }
        }.toMap

        val newSto = sto ++ defs.flatMap{
          case Lazy(name, expr) => {
            val addr = newEnv(name)
            List(addr -> ExprV(expr, newEnv))
          }
          case RecFun(name, params, expr) => {
            val addr = newEnv(name)
            List(addr -> CloV(params, expr, newEnv))
          }
          case TypeDef(variants) => variants.map{
            case Variant(vname, _) => {
              val addr = newEnv(vname)
              (addr -> ConstructorV(vname))
            }
          }
        }
        interp(body, newEnv, newSto)
      }
      case Assign(name, expr) => {
        env.get(name) match {
          case Some(addr) => {
            val (ev, es) = interp(expr, env, sto)
            (ev, es + (addr -> ev))
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
            val newEnv = fenv ++ (params zip argVals).map{
              case (name, value) => (name -> malloc(as))
            }
            val newSto = as ++ (params zip argVals).map{
              case (name, value) => (newEnv(name) -> value)
            }
            interp(body, newEnv, newSto)
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
            val newEnv = env ++ (names zip values).map{
              case (name, value) => (name -> malloc(es))
            }
            val newSto = es ++ (names zip values).map{
              case (name, value) => (newEnv(name) -> value)
            }
            interp(body, newEnv, newSto)
          }
          case _ => error("not a variant value")
        }
      }
    }
  }
}