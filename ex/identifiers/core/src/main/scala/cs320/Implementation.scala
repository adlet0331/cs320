package cs320

object Implementation extends Template {

  def freeIds(expr: Expr): Set[String] = {
    def frees(expr: Expr, env: Set[String]): Set[String] = expr match{
      case Num(_) => Set()
      case Add(l, r) => frees(l, env) ++ frees(r, env)
      case Sub(l, r) => frees(l, env) ++ frees(r, env)
      case Id(id) => if(env.contains(id)) Set() else Set(id)
      case Val(name, value, body) => frees(value, env) ++ frees(body, env + name)
    }
    frees(expr, Set())
  }

  def bindingIds(expr: Expr): Set[String] = expr match{
    case Num(_) => Set()
    case Add(l, r) => bindingIds(l) ++ bindingIds(r)
    case Sub(l, r) => bindingIds(l) ++ bindingIds(r)
    case Id(id) => Set()
    case Val(name, value, body) => Set(name) ++ bindingIds(value) ++ bindingIds(body)
  }

  def boundIds(expr: Expr): Set[String] = {
    def bounds(expr: Expr, env: Set[String]): Set[String] = expr match{
      case Num(_) => Set()
      case Add(l, r) => bounds(l, env) ++ bounds(r, env)
      case Sub(l, r) => bounds(l, env) ++ bounds(r, env)
      case Id(id) => if(env.contains(id)) Set(id) else Set()
      case Val(name, value, body) => bounds(value, env) ++ bounds(body, env + name)
    }
    bounds(expr, Set())
  }
}
