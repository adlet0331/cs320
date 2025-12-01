package cs320

object Implementation extends Template {

  // apply a binary numeric function on all the combinations of numbers from
  // the two input lists, and return the list of all the results
  def binOp(
    op: (Int, Int) => Int,
    ls: List[Int],
    rs: List[Int]
  ): List[Int] = ls match {
    case Nil => Nil
    case l :: rest =>
      def f(r: Int): Int = op(l, r)
      rs.map(f) ++ binOp(op, rest, rs)
  }

  def interp(expr: Expr): List[Int] = {
    def interpEnv(expr: Expr, env: Map[String, List[Int]]) : List[Int] = expr match {
      case Num(n) => n
      case Add(l, r) => binOp((x, y) => x + y, interpEnv(l, env), interpEnv(r, env))
      case Sub(l, r) => binOp((x, y) => x - y, interpEnv(l, env), interpEnv(r, env))
      case Val(name, value, body) => interpEnv(body, env + (name -> interpEnv(value, env)))
      case Id(name) => env.getOrElse(name, error(s"free identifier: $name"))
      case Min(l, m, r) => binOp((x, y) => Math.min(x, y), binOp((x, y) => Math.min(x, y), interpEnv(l, env), interpEnv(m, env)), interpEnv(r, env))
      case Max(l, m, r) => binOp((x, y) => Math.max(x, y), binOp((x, y) => Math.max(x, y), interpEnv(l, env), interpEnv(m, env)), interpEnv(r, env))
    }
    interpEnv(expr, Map())
  }
}
