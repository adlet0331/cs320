package cs320

trait Template {

  def run(str: String): List[Int] = interp(Expr(str))

  def interp(expr: Expr): List[Int]
}
