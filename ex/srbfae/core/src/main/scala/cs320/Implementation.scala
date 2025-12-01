package cs320

import Value._

object Implementation extends Template {
  def numVop(op: (Int, Int) => Int): (Value, Value) => NumV = (_, _) match {
    case (NumV(x), NumV(y)) => NumV(op(x, y))
    case (x, y) => error(s"not both numbers")
  }
  val intAdd = numVop(_ + _)
  val intSub = numVop(_ - _)

  type Sto = Map[Addr, Value]
  def malloc(sto: Sto): Addr = sto.foldLeft(0){
    case (max, (addr, _)) => Math.max(max, addr)
  } + 1

  def interp(expr: Expr): Value = interp(expr, Map(), Map())._1

  def interp(expr: Expr, env: Env, sto: Sto): (Value, Sto) = expr match {
    case Num(numv) => (NumV(numv), sto)
    case Add(left, right) => {
      val (lv, ls) = interp(left, env, sto)
      val (rv, rs) = interp(right, env, ls)
      (intAdd(lv, rv), rs)
    }
    case Sub(left, right) => {
      val (lv, ls) = interp(left, env, sto)
      val (rv, rs) = interp(right, env, ls)
      (intSub(lv, rv), rs)
    }
    case Id(name) => (env.getOrElse(name, error("Free identifier")), sto)
    case Fun(param, body) => (CloV(param, body, env), sto)
    case App(fun, arg) => interp(fun, env, sto) match {
      case (CloV(param, body, fenv), cs)=> {
        val (argv, args) = interp(arg, env, cs)
        interp(body, fenv + (param -> argv), args)
      }
      case v => error("Not CloV")
    }
    case NewBox(expr) => {
      val (eval, esto) = interp(expr, env, sto)
      val maddr = malloc(esto)
      (BoxV(maddr), esto + (maddr -> eval))
    }
    case SetBox(box, expr) => interp(box, env, sto) match {
      case (BoxV(baddr), bs) => {
        val (eval, es) = interp(expr, env, bs)
        (eval, es + (baddr -> eval))
      }
      case v => error("Not a Box")
    }
    case OpenBox(box) => interp(box, env, sto) match {
      case (BoxV(baddr), bs) => {
        (bs.getOrElse(baddr, error("No Val in Addr")), bs)
      }
      case v => error("Not a Box")
    }
    case Seqn(left, right) => {
      val lvs = interp(left, env, sto)
      right.foldLeft(lvs){
        case ((_, befs), e) => interp(e, env, befs)
      }
    }
    case Rec(fields) => {
      fields.foldLeft((RecV(Map[String, Addr]()), sto)){
        case ((RecV(rec), bs), (name, expr)) => {
          val (ev, es) = interp(expr, env, bs)
          val addr = malloc(es)
          (RecV(rec + (name -> addr)), es + (addr -> ev))
        }
      }
    }
    case Get(record, field) => interp(record, env, sto) match {
      case (RecV(fields), rs) => {
        val addr: Addr = fields.getOrElse(field, error("no such field"))
        (rs.getOrElse(addr, error("No Address")), rs)
      }
    }
    case Set(record, field, expr) => interp(record, env, sto) match {
      case (RecV(fields), news) => {
        val (ev, es) = interp(expr, env, news)
        val addr: Addr = fields.getOrElse(field, error("no such field"))
        (RecV(fields), es + (addr -> ev))
      }
    }
  }
}
