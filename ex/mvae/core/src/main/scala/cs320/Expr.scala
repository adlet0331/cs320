package cs320

import scala.util.parsing.combinator._

sealed trait Expr

case class Num(values: List[Int]) extends Expr
case class Add(left: Expr, right: Expr) extends Expr
case class Sub(left: Expr, right: Expr) extends Expr
case class Val(name: String, expr: Expr, body: Expr) extends Expr
case class Id(id: String) extends Expr
case class Min(left: Expr, mid: Expr, right: Expr) extends Expr
case class Max(left: Expr, mid: Expr, right: Expr) extends Expr

object Expr extends RegexParsers {

  def wrapC[T](rule: Parser[T]): Parser[T] = "{" ~> rule <~ "}"
  def wrapR[T](rule: Parser[T]): Parser[T] = "(" ~> rule <~ ")"

  lazy val int: Parser[Int] = """-?\d+""".r ^^ (_.toInt)

  val keywords = Set("val", "min", "max")

  lazy val str: Parser[String] =
    "[a-zA-Z_][a-zA-Z0-9_]*".r.withFilter(!keywords.contains(_))

  lazy val expr: Parser[Expr] =
    int ^^ (n => Num(List(n))) |
    wrapR(repsep(int, ",")) ^^ Num |
    wrapR((expr <~ "+") ~ expr) ^^ { case l ~ r => Add(l, r) } |
    wrapR((expr <~ "-") ~ expr) ^^ { case l ~ r => Sub(l, r) } |
    wrapC(("val" ~> str <~ "=") ~ (expr <~ ";") ~ expr) ^^
      { case x ~ i ~ b => Val(x, i, b) } |
    "min" ~> wrapR(expr ~ ("," ~> expr <~ ",") ~ expr) ^^
      { case l ~ m ~ r => Min(l, m, r) } |
    "max" ~> wrapR(expr ~ ("," ~> expr <~ ",") ~ expr) ^^
      { case l ~ m ~ r => Max(l, m, r) } |
    str ^^ Id

  def apply(str: String): Expr = parseAll(expr, str).get
}
