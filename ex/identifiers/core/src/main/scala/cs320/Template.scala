package cs320

trait Template {

  def freeIds(expr: Expr): Set[String]

  def bindingIds(expr: Expr): Set[String]

  def boundIds(expr: Expr): Set[String]
}
