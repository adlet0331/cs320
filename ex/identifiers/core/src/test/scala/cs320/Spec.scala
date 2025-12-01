package cs320

import Macros._
import Implementation._

class Spec extends SpecBase {

  test(freeIds(Expr("{ val x = 3; (x + (3 - x)) }")), Set())
  test(freeIds(Expr("{ val x = 3; (a - (4 + x)) }")), Set("a"))
  test(freeIds(Expr("{ val x = 3; (b - (a - x)) }")), Set("a", "b"))
  test(freeIds(Expr("{ val x = 3; (a - (b - (x + b))) }")), Set("a", "b"))
  test(freeIds(Expr("{ val x = 3; (y - { val y = 7; (x + (b - a)) }) }")), Set("a", "b", "y"))
  test(freeIds(Expr("{ val x = t; (x - { val y = y; (x + (b - a)) }) }")), Set("a", "b", "t", "y"))
  test(freeIds(Expr("{ val x = { val y = 3; (x - y) }; (x + y) }")), Set("x", "y"))
  test(freeIds(Expr("({ val x = 10; { val x = 3; (y - { val y = 7; (x + (c - b)) }) } } + { val a = a; a })")), Set("a", "b", "c", "y"))
  test(freeIds(Expr("({ val x = 10; { val x = 3; (y - { val y = 7; (x + (c - b)) }) } } + { val a = d; a })")), Set("b", "c", "d", "y"))
  test(freeIds(Expr("({ val x = 10; { val x = 3; (y - { val y = 7; (x + (c - b)) }) } } + { val a = d; z })")), Set("b", "c", "d", "y", "z"))

  test(bindingIds(Expr("(3 + (x - y))")), Set())
  test(bindingIds(Expr("{ val y = 3; { val x = x; y } }")), Set("x", "y"))
  test(bindingIds(Expr("{ val y = 3; { val y = x; (x + y) } }")), Set("y"))
  test(bindingIds(Expr("{ val y = 3; { val y = { val x = (3 + y); (x - y) }; (x + y) } }")), Set("x", "y"))
  test(bindingIds(Expr("{ val z = 3; { val w = { val z = (3 + y); (x - y) }; { val w = y; (7 + w) } } }")), Set("w", "z"))

  test(boundIds(Expr("{ val x = 3; (y + 3) }")), Set())
  test(boundIds(Expr("{ val x = 3; (x + (x - y)) }")), Set("x"))
  test(boundIds(Expr("{ val x = 3; (x + { val y = 7; (x - y) }) }")), Set("x", "y"))
  test(boundIds(Expr("{ val x = 3; { val y = x; (3 - y) } }")), Set("x", "y"))
  test(boundIds(Expr("{ val x = 3; (y + { val y = x; (3 - 7) }) }")), Set("x"))
  test(boundIds(Expr("{ val x = x; (y + { val y = y; (3 - { val z = 7; (z - x) }) }) }")), Set("x", "z"))
  test(boundIds(Expr("{ val x = { val y = 3; (x + y) }; (y + { val y = y; (3 - 7) }) }")), Set("y"))
  test(boundIds(Expr("{ val x = a; { val y = b; { val z = c; (d + (x - (y + z))) } } }")), Set("x", "y", "z"))
  test(boundIds(Expr("({ val x = 10; { val x = 3; (y - { val y = 7; (x + (c - b)) }) } } + { val a = d; a })")), Set("a", "x"))
  test(boundIds(Expr("({ val x = 10; { val x = 3; (y - { val y = 7; (x + (c - b)) }) } } + { val a = d; z })")), Set("x"))

  /* Write your own tests */
}
