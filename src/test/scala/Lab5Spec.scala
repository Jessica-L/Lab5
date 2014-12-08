import org.scalatest._
import jsy.lab5.ast._
import Lab5._

class Lab5Spec extends FlatSpec {
  
  "mapFirstDoWith" should "map the first element where f returns Some" in {
     val l1 = List(1, 2, -3, 4, -5)
     val gold1 = List(1, 2, 3, 4, -5)
     def dowith[W]: DoWith[W,List[Int]] = mapFirstWith[W,Int] { (i: Int) => if (i < 0) Some(doreturn(-i)) else None } (l1)
     assertResult((true,gold1)) { dowith(true) }
     assertResult((42,gold1)) { dowith(42) }
  }
  
  "DoGetField" should "access a field from an object in memory" in {
    val setup = Obj(Map("a" -> N(42), "b" -> N(47)))
    val (m:Mem, addr: A) = step(setup)(Mem.empty)
    val e = GetField(addr, "b")
    val (mp, ep: Expr) = step(e)(m)
    assert(m == mp)
    assertResult(N(47)) { ep }
  }

  "DoVar" should "declare a variable" in {
    val e = Decl(MVar, "x", N(10), Var("x"))
    val (mp: Mem, ep: Expr) = step(e)(Mem.empty)
    assert(ep match {
      case Unary(Deref, a@A(_)) =>
        // Verify memory correctly references N(10)
        mp.get(a).get == N(10)
      case _ => false
      })
  }

  "SearchCall1" should "step its function" in {
    val e = Call(If(B(true),Function(None,Left(List(("n",TNumber))),None,Var("n")),Null),List(N(42)))
    val (_, ep: Expr) = step(e)(Mem.empty)
    assertResult(Call(Function(None, Left(List(("n", TNumber))), None, Var("n")), List(N(42)))) { ep }    
  }
}
