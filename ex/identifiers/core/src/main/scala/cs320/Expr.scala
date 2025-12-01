package cs320

import scala.util.parsing.combinator._

sealed trait Expr

case class Num(value: Int) extends Expr
case class Add(left: Expr, right: Expr) extends Expr
case class Sub(left: Expr, right: Expr) extends Expr
case class Id(id: String) extends Expr
case class Val(name: String, expr: Expr, body: Expr) extends Expr

object Expr extends RegexParsers {

  def wrapC[T](rule: Parser[T]): Parser[T] = "{" ~> rule <~ "}"
  def wrapR[T](rule: Parser[T]): Parser[T] = "(" ~> rule <~ ")"

  lazy val int: Parser[Int] = """-?\d+""".r ^^ (_.toInt)

  lazy val str: Parser[String] =
  "[a-zA-Z_][a-zA-Z0-9_]*".r.withFilter(_ != "val")

  lazy val expr: Parser[Expr] =
    int ^^ Num |
    wrapR((expr <~ "+") ~ expr) ^^ { case l ~ r => Add(l, r) } |
    wrapR((expr <~ "-") ~ expr) ^^ { case l ~ r => Sub(l, r) } |
    wrapC(("val" ~> str <~ "=") ~ (expr <~ ";") ~ expr) ^^
      { case x ~ i ~ b => Val(x, i, b) } |
    str ^^ Id

  def apply(str: String): Expr = parseAll(expr, str).get
}
