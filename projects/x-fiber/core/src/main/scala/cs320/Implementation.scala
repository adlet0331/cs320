package cs320

import Value._

object Implementation extends Template {
  def numVop(op: (BigInt, BigInt) => BigInt): (Value, Value) => IntV = (_, _) match {
    case (IntV(x), IntV(y)) => IntV(op(x, y))
    case (x, y) => error(s"not both numbers")
  }
  def numBop(op: (BigInt, BigInt) => Boolean): (Value, Value) => BooleanV = (_, _) match {
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
  val intEq = numBop(_ == _)
  val intLt = numBop(_ < _)

  def interp(expr: Expr): Value = interp(expr, Map(), v => v)
  def interp(expr: Expr, env: Env, cont: Cont): Value = interp(expr, env, cont, v => error("uncaught exception"))

  def interp(expr: Expr, env: Env, cont: Cont, econt: Cont): Value = expr match {
    // Value cases
    case Id(name) => cont(env.getOrElse(name, error(s"free identifier: $name")))
    case IntE(value) => cont(IntV(value))
    case BooleanE(value) => cont(BooleanV(value))
    case TupleE(value) => {
      def evalArgsCPS(args: List[Expr], k_list: List[Value] => Value): Value = {
        args match {
          case Nil => k_list(Nil)
          case h :: t =>
            interp(h, env, hv => {
              evalArgsCPS(t, tvs => {
                k_list(hv :: tvs)
              })
            }, econt)
        }
      }
      evalArgsCPS(value, vs => cont(TupleV(vs)))
    }
    case NilE => cont(NilV)
    case ConsE(head, tail) => interp(head, env, h => 
        interp(tail, env, t => t match {
              case NilV => cont(ConsV(h, NilV))
              case ConsV(_, _) => cont(ConsV(h, t))
              case v => error(s"not a ConsV or NilV")
            }, econt
        ), econt)
    case Fun(params, body) => cont(CloV(params, body, env))
    case RecFuns(functions, body) => {
      // Create new environment with all functions bound
      val newEnv = env ++ functions.map({
        case FunDef(name, params, body) => (name -> CloV(params, body, env))
        case v => error(s"not a FunDef")
      })
      for (FunDef(name, params, body) <- functions){
        newEnv(name) match {
          case c @ CloV(_, _, _) => c.env = newEnv
          case _ => error("Impossible error")
        }
      }
      interp(body, newEnv, cont, econt)
    }

    // Operations
    case Add(left, right) => interp(left, env, v1 => interp(right, env, v2 => {
      cont(intAdd(v1, v2))
    }, econt), econt)
    case Mul(left, right) => interp(left, env, v1 => interp(right, env, v2 => {
      cont(intMul(v1, v2))
    }, econt), econt)
    case Div(left, right) => interp(left, env, v1 => interp(right, env, v2 => {
      cont(intDiv(v1, v2))
    }, econt), econt)
    case Mod(left, right) => interp(left, env, v1 => interp(right, env, v2 => {
      cont(intMod(v1, v2))
    }, econt), econt)
    case Eq(left, right) => interp(left, env, v1 => interp(right, env, v2 => {
      cont(intEq(v1, v2))
    }, econt), econt)
    case Lt(left, right) => interp(left, env, v1 => interp(right, env, v2 => {
      cont(intLt(v1, v2))
    }, econt), econt)
    // Control flow
    case If(cond, tBranch, fBranch) =>{
      interp(cond, env, v => v match{
        case BooleanV(b) => {
          if (b) interp(tBranch, env, cont, econt)
          else interp(fBranch, env, cont, econt)
        }
        case _ => error(s"not a boolean")
      }, econt)
    }
    case Proj(expr, index) => interp(expr, env, tv => tv match {
      case TupleV(values) =>
        if (index < 1 || index > values.length) error(s"tuple index out of bounds: $index")
        else cont(values(index - 1))
      case v => error(s"not a tuple")
    }, econt)
    case Empty(expr) => interp(expr, env, cv => cv match {
      case NilV => cont(BooleanV(true))
      case ConsV(_, _) => cont(BooleanV(false))
      case v => error(s"not a consV")
    }, econt)
    case Head(expr) => interp(expr, env, v => {
      v match {
        case ConsV(head, tail) => cont(head)
        case v => error(s"not a consV")
      }
    }, econt)
    case Tail(expr) => interp(expr, env, v => {
      v match {
        case ConsV(head, tail) => cont(tail)
        case v => error(s"not a consV")
      }
    }, econt)
    case Val(name, expression, body) =>
      interp(expression, env, v => interp(body, env + (name -> v), cont, econt), econt)
    case Vcc(name, body) => interp(body, env + (name -> ContV(cont)), cont, econt)
    case App(function, arguments) => {
      interp(function, env, fv => {
        def evalArgsCPS(args: List[Expr], k_list: List[Value] => Value): Value = {
          args match {
            case Nil => k_list(Nil)
            case h :: t =>
              interp(h, env, hv => {
                evalArgsCPS(t, tvs => {
                  k_list(hv :: tvs)
                })
              }, econt)
          }
        }
        evalArgsCPS(arguments, argValues => {
          fv match {
            case CloV(params, body, fenv) => {
              if (params.length != argValues.length) error(s"argument length mismatch")
              val newEnv = fenv ++ params.zip(argValues)
              interp(body, newEnv, cont, econt)
            }
            case ContV(k) => {
              if (argValues.length != 1) error(s"continuation application must have exactly one argument")
              k(argValues.head)
            }
            case v => error(s"not a function or continuation")
        }
        })
      }, econt)
    }
    case Throw(expression) => interp(expression, env, v => econt(v), econt)
    case Try(tryexpr, handler) => 
      interp(tryexpr, env, cont, v => 
        interp(handler, env, hv => hv match {
          case CloV(params, body, henv) => {
            if (params.length != 1) error(s"handler must have exactly one parameter")
            val newEnv = henv + (params.head -> v)
            interp(body, newEnv, cont, econt)
          }
          case ContV(k) => k(v) 
          case v => error(s"not a function")
        }, econt))
    case Test(expression, typ) => interp(expression, env, v => v match {
      case IntV(_) => cont(BooleanV(typ == IntT))
      case BooleanV(_) => cont(BooleanV(typ == BooleanT))
      case TupleV(_) => cont(BooleanV(typ == TupleT))
      case ConsV(_, _) => cont(BooleanV(typ == ListT))
      case NilV => cont(BooleanV(typ == ListT))
      case CloV(_,_,_) => cont(BooleanV(typ == FunctionT))
      case ContV(_) => cont(BooleanV(typ == FunctionT))
    }, econt)
  }
}