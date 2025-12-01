package cs320

sealed trait Value

object Value {

  type Env = Map[String, Value]

  case class NumV(n: Int) extends Value
  case class CloV(params: List[String], body: Expr, env: Env) extends Value
  case class RecV(map: Map[String, Value]) extends Value

  def show(value: Value): String = value match {
    case NumV(n) => n.toString
    case _: CloV => "<function>"
    case RecV(m) => m.toList.sortBy(_._1).map{
      case (k, v) => s"$k = ${show(v)}"
    }.mkString("{ ", ", ", " }")
  }

}
