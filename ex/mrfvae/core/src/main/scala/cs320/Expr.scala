package cs320

import scala.util.parsing.combinator._

sealed trait Expr

case class Num(num: Int) extends Expr
case class Add(left: Expr, right: Expr) extends Expr
case class Sub(left: Expr, right: Expr) extends Expr
case class Val(name: String, value: Expr, body: Expr) extends Expr
case class Id(name: String) extends Expr
case class App(func: Expr, args: List[Expr]) extends Expr
case class Fun(params: List[String], body: Expr) extends Expr
case class Rec(rec: Map[String, Expr]) extends Expr
case class Acc(expr: Expr, name: String) extends Expr

object Expr extends RegexParsers {

  def wrapC[T](rule: Parser[T]): Parser[T] = "{" ~> rule <~ "}"
  def wrapR[T](rule: Parser[T]): Parser[T] = "(" ~> rule <~ ")"

  lazy val int: Parser[Int] = """-?\d+""".r ^^ (_.toInt)

  val keywords = Set("val")

  lazy val str: Parser[String] =
    "[a-zA-Z_][a-zA-Z0-9_]*".r.withFilter(!keywords(_))

  lazy val expr: Parser[Expr] =
    e1 ~ rep(
      wrapR(repsep(expr, ",")) ^^ EApp |
      "." ~> str ^^ EAcc
    ) ^^ { case e ~ es => es.foldLeft(e){
      case (e, EApp(as)) => App(e, as)
      case (e, EAcc(f)) => Acc(e, f)
    }}

  lazy val e1: Parser[Expr] =
    int ^^ Num | str ^^ Id |
    wrapR((expr <~ "+") ~ expr) ^^ { case l ~ r => Add(l, r) } |
    wrapR((expr <~ "-") ~ expr) ^^ { case l ~ r => Sub(l, r) } |
    wrapC(("val" ~> str <~ "=") ~ (expr <~ ";") ~ expr) ^^
      { case x ~ i ~ b => Val(x, i, b) } |
    wrapC(str ~ ("=>" ~> expr)) ^^ { case p ~ b => Fun(p :: Nil, b) } |
    wrapC(wrapR(repsep(str, ",")) ~ ("=>" ~> expr)) ^^ {
      case ps ~ b =>
        if (dupCheck(ps)) error(s"bad syntax: duplicate parameters: $ps")
        Fun(ps, b)
    } |
    wrapC(repsep(str ~ ("=" ~> expr), ",")) ^^ (fs => {
      val l = fs.map{ case f ~ e => (f, e) }
      val ns = l.map(_._1)
      if (dupCheck(ns)) error(s"duplicate fields: $ns")
      Rec(l.toMap)
    })

  sealed trait E
  case class EApp(as: List[Expr]) extends E
  case class EAcc(f: String) extends E

  def dupCheck(ss: List[String]): Boolean = ss.distinct.length != ss.length

  def apply(str: String): Expr = parseAll(expr, str).get
}
