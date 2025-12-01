package cs320

import Value._

object Implementation extends Template {
  def interp(expr: Expr): Value = interp(expr, Map())

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

  def interp(expr: Expr, env: Env): Value = expr match {
    // Value cases
    case Id(name) => env.getOrElse(name, error(s"free identifier: $name"))
    case IntE(value) => IntV(value)
    case BooleanE(value) => BooleanV(value)
    case TupleE(value) => TupleV(value.map(interp(_, env)))
    case NilE => NilV
    case ConsE(head, tail) =>{
      val h = interp(head, env)
      val t = interp(tail, env)
      t match {
        case NilV => ConsV(h, NilV)
        case ConsV(_, _) => ConsV(h, t)
        case v => error(s"not a ConsV or NilV")
      }
    } 
    case Fun(params, body) => CloV(params, body, env)
    case RecFuns(functions, body) => {
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
      interp(body, newEnv)
    }
    // Operations
    case Add(left, right) => intAdd(interp(left, env), interp(right, env))
    case Mul(left, right) => intMul(interp(left, env), interp(right, env))
    case Div(left, right) => intDiv(interp(left, env), interp(right, env))
    case Mod(left, right) => intMod(interp(left, env), interp(right, env))
    case Eq(left, right) => intEq(interp(left, env), interp(right, env))
    case Lt(left, right) => intLt(interp(left, env), interp(right, env))
    // Control flow
    case If(cond, tBranch, fBranch) => interp(cond, env) match {
      case BooleanV(true) => interp(tBranch, env)
      case BooleanV(false) => interp(fBranch, env)
      case v => error(s"not a boolean")
    }
    case Proj(expr, index) => interp(expr, env) match {
      case TupleV(values) =>
        if (index < 1 || index > values.length) error(s"tuple index out of bounds: $index")
        else values(index - 1)
      case v => error(s"not a tuple")
    }
    case Empty(expr) => interp(expr, env) match {
      case NilV => BooleanV(true)
      case ConsV(head, tail) => BooleanV(false)
      case v => error(s"not a consV")
    }
    case Head(expr) => {
      val v = interp(expr, env)
      v match {
        case ConsV(head, tail) => head
        case v => error(s"not a consV")
      }
    } 
    case Tail(expr) => {
      val v = interp(expr, env)
      v match {
        case ConsV(head, tail) => tail
        case v => error(s"not a consV")
      }
    } 
    case Val(name, expression, body) => interp(body, env + (name -> interp(expression, env)))
    case App(function, arguments) => interp(function, env) match {
      case CloV(params, body, fenv) => {
        if (arguments.length != params.length) error("arguments length is not matched")
        val argVals = arguments.map(interp(_, env))
        interp(body, fenv ++ params.zip(argVals))
      }
      case v => error(s"not a CloV:")
    }
    case Test(expression, typ) => interp(expression, env) match{
      case IntV(_) => BooleanV(typ == IntT)
      case BooleanV(_) => BooleanV(typ == BooleanT)
      case TupleV(_) => BooleanV(typ == TupleT)
      case ConsV(_, _) => BooleanV(typ == ListT)
      case NilV => BooleanV(typ == ListT)
      case CloV(_,_,_) => BooleanV(typ == FunctionT)
    }
  }
}