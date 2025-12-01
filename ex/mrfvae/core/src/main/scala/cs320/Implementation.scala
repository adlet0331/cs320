package cs320

import Value._

object Implementation extends Template {

  def interp(expr: Expr): Value = {
    def interpEnv(expr: Expr, env: Env): Value = expr match{
      case Num(n) => NumV(n)
      case Add(l, r) => (interpEnv(l, env), interpEnv(r, env)) match {
        case (NumV(n1), NumV(n2)) => NumV(n1 + n2)
        case _ => error(s"not both numbers:${Value.show(interpEnv(l, env))}, ${Value.show(interpEnv(r, env))}")
      }
      case Sub(l, r) => (interpEnv(l, env), interpEnv(r, env)) match {
        case (NumV(n1), NumV(n2)) => NumV(n1 - n2)
        case _ => error(s"not both numbers:${Value.show(interpEnv(l, env))}, ${Value.show(interpEnv(r, env))}")
      }
      case Val(name, value, body) => interpEnv(body, env + (name -> interpEnv(value, env)))
      case Id(name) => env.getOrElse(name, error(s"free identifier: $name"))
      case Fun(params, body) => CloV(params, body, env)
      case App(func, args) => interpEnv(func, env) match {
        case CloV(params, body, fenv) => {
          if (params.length == args.length && params.length == 0)
            interpEnv(body, fenv)
          if (params.length != args.length)
            error(s"wrong arity: expected ${params.length}, found ${args.length}")
          val argVals = args.map(interpEnv(_, env))
          interpEnv(body, fenv ++ params.zip(argVals))
        }
        case _ => error(s"not a closure: ${Value.show(interpEnv(func, env))}")
      }
      case Rec(map) => RecV(map.map{ 
        case (key, vexpr) => (key, interpEnv(vexpr, env)) 
      })
      case Acc(expr, name) => interpEnv(expr, env) match {
        case RecV(map) => map.getOrElse(name, error(s"no such field: $name"))
        case _ => error("not a record")
      }
    }
    interpEnv(expr, Map())
  }
}
