package cs320

import Macros._

class Spec extends SpecBase {

  val run = Implementation.run _

  test(run("{ a = 10, b = (1 + 2) }"), "{ a = 10, b = 3 }")
  test(run("{ a = 10, b = (1 + 2) }.b"), "3")
  test(run("{ val g = { r => r.c }; g({ a = 0, c = 12, b = 7 }) }"), "12")
  test(run("{ r = { z = 0 } }.r"), "{ z = 0 }")
  test(run("{ r = { z = 0 } }.r.z"), "0")
  test(run("{ val f = { (a, b) => (a + b) }; { val g = { x => (x - 5) }; { val x = f(2, 5); g(x) } } }"), "2")
  test(run("{ val f = { (x, y) => (x + y) }; f(1, 2) }"), "3")
  test(run("{ val f = { () => 5 }; (f() + f()) }"), "10")
  test(run("{ val h = { (x, y, z, w) => (x + w) }; h(1, 4, 5, 6) }"), "7")
  test(run("{ val f = { () => 4 }; { val g = { x => (x + x) }; { val x = 10; ((x + f()) - g(4)) } } }"), "6")
  test(run("{ val x = 3; { val y = 5; { a = x, b = y }.a } }"), "3")
  test(run("{ val f = { (a, b) => (a.a + b) }; { val g = { x => (5 + x) }; { val x = f({ a = 10, b = 5 }, 2); g(x) } } }"), "17")
  test(run("{ val f = { (a, b, c, d, e) => { a = a, b = b, c = c, d = d, e = e } }; f(1, 2, 3, 4, 5).c }"), "3")
  test(run("{ val f = { (a, b, c) => { a = a, b = b, c = c } }; f(1, 2, 3).b }"), "2")
  test(run("{ val f = { (a, b, c) => { x = a, y = b, z = c, d = 2, e = 3 } }; f(1, 2, 3).y }"), "2")
  test(run("{ val f = { x => (5 + x) }; f({ a = { a = 10, b = (5 - 2) }, b = { x = 50 }.x }.a.b) }"), "8")
  test(run("{ a = 10 }"), "{ a = 10 }")
  test(run("{ a = 10 }.a"), "10")
  test(run("{ a = (1 + 2) }.a"), "3")
  test(run("{ x => x }"), "<function>")
  test(run("{ a = { b = 10 } }.a"), "{ b = 10 }")
  test(run("{ a = { a = 10 } }.a.a"), "10")
  test(run("{ a = { a = 10, b = 20 } }.a.a"), "10")
  test(run("{ a = { a = 10, b = 20 } }.a.b"), "20")
  test(run("({ a = 10 }.a + { a = 20 }.a)"), "30")
  test(run("{ a = (2 - 1) }"), "{ a = 1 }")
  test(run("{ a = (2 - 1) }.a"), "1")
  test(run("{ val y = { x = 1, y = 2, z = 3 }; y.y }"), "2")
  test(run("{ val y = { x = 1, y = 2, z = 3 }; y.z }"), "3")

  testExc(run("2((3 + 4))"), "not a closure")
  testExc(run("{ (x, y) => (x + y) }(1)"), "wrong arity")
  testExc(run("(1 + 2).a"), "not a record")
  testExc(run("{ z = { z = 0 }.y }"), "no such field")

  /* Write your own tests */
}
