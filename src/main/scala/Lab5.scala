object Lab5 extends jsy.util.JsyApplication {
  import jsy.lab5.ast._
  import jsy.lab5._
  
  /*
   * CSCI 3155: Lab 5
   * Jessica Lynch
   * 
   * Partner: Andrew Gordon
   * Collaborators: Erik Eakins, Noah Dillon, Catherine Dewerd, Max Harris
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * throws new UnsupportedOperationException as needed to get something
   * that compiles without error.
   */
  
  /*** Helper: mapFirst to DoWith ***/
  
  
  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](f: A => Option[DoWith[W,A]])(l: List[A]): DoWith[W,List[A]] = l match {
    case Nil => doreturn(l) //Return list if empty or if we've reached its end.
    case h :: t => f(h) match { //If list not empty, pattenr match on head.
      case None => mapFirstWith(f)(t).map((alpha:List[A]) => (h::alpha)) //Continue if no match found.
      case Some(withhp) => withhp.map((alpha:A)=>(alpha::t)) //If match found, modify alpha and map it to tail.
    }
  }


  /*** Casting ***/
  
  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
    case (TNull, TObj(_)) => true
    case (_, _) if (t1 == t2) => true
    //for all objects in field 1:
    case (TObj(fields1), TObj(fields2)) => fields1.forall {
      //if type2 is nothing, return true (can cast to Nonetype)
      case(type1, type2) if (type2 == None) => true
      //if it is something, check for t1 field type
      case(type1, type2) => fields2.get(type1) match {
        case None => true
        //if there is something there, compare type2 to a new type
        case Some(type3) => castOk(type2, type3)
      }
    }
    case (TInterface(tvar, t1p), _) => castOk(typSubstitute(t1p, t1, tvar), t2)
    case (_, TInterface(tvar, t2p)) => castOk(t1, typSubstitute(t2p, t2, tvar))
    case _ => false
  }
  
  /*** Type Inference ***/
  
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  } 
    
  def mut(m: PMode): Mutability = m match {
    case PName => MConst
    case PVar | PRef => MVar
  }
  
  def typeInfer(env: Map[String,(Mutability,Typ)], e: Expr): Typ = {
    
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw new StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Null => TNull
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) =>
        val (_, t) = env(x)
        t
      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typ(e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Unary(Cast(e1), e2) => (castOk(typ(e2), e1)) match {
        case true => e1; //if a valid cast, return e1 
        case false => err(typ(e2), e2); //if invalid, return an error on e2 
      }
      case Binary(Plus, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match {
          case TNumber => TNumber
          case tgot => err(tgot, e2)
        }
        case TString => typ(e2) match {
          case TString => TString
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match {
          case TNumber => TNumber
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Eq|Ne, e1, e2) => typ(e1) match {
        case t1 if !hasFunctionTyp(t1) => typ(e2) match {
          case t2 if (t1 == t2) => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match {
          case TNumber => TBool
          case tgot => err(tgot, e2)
        }
        case TString => typ(e2) match {
          case TString => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(And|Or, e1, e2) => typ(e1) match {
        case TBool => typ(e2) match {
          case TBool => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Seq, e1, e2) => typ(e1); typ(e2)
      case If(e1, e2, e3) => typ(e1) match {
        case TBool =>
          val (t2, t3) = (typ(e2), typ(e3))
          if (t2 == t3) t2 else err(t3, e3)
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields map { case (f,t) => (f, typ(t)) })
      
      case GetField(e1, f) => typ(e1) match {
        case TObj(tfields) if (tfields.contains(f)) => tfields(f)
        case tgot => err(tgot, e1)
      } 
      
      case Function(p, paramse, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(rt)) =>
            val tprime = TFunction(paramse, rt)
            env + (f -> (MConst, tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with the parameters.
        val env2 = paramse match {
          case Left(params) => params.foldLeft(env1)({
            case(environment, parameter) => parameter match {
              //pass types of type 1 to new environment
              case(type1, type2) => environment + (type1 -> (MConst, type2))
            }      
          })
          case Right((mode,x,t)) => mode match {
            //pass by name: extend env1 with x mapped to t as MConst
            case PName => env1 + (x -> (MConst, t))
            //pass by variable or reference: pass by MVar
            case _ => env1 + (x -> (MVar, t))
          }
        }
        // Infer the type of the function body
        val t1 = typeInfer(env2, e1)
        tann foreach { rt => if (rt != t1) err(t1, e1) };
        TFunction(paramse, t1)
      }
      
      case Call(e1, args) => typ(e1) match {
        case TFunction(Left(params), tret) if (params.length == args.length) => {
          (params, args).zipped.foreach {
            (paramX, argY) => (paramX, argY) match {
              case((str, typParam), typArg) => if (typParam != typ(typArg)) err(typParam, typArg)
            }
          }
          tret
        }
        case tgot @ TFunction(Right((mode,_,tparam)), tret) => mode match { 
          case badcall if (args.length == 0) => err(tparam,e1) //Return error if args missing.
          //Check mutability types for pass by name or value; if mismatched, return error
          case (PName | PVar) => args.head match {
            case e => if (tparam == typ(e)) typ(e) else err(tparam, e1)
          }
          //Check pass by ref conditions hold true -- must be a location expression -- and
          //check mutability types; if types mismatched, return error
          case PRef => args.head match {
            case a => if (isLExpr(a) &&  tparam == typ(a)) tret else err(tparam, e1)
          }
        }
        case tgot => err(tgot, e1)
      }
      /* TYPE DECL (Declaration): name of variable x is mapped mode and type of e1
       * which is extended to the environment env to then infer type of e2.
       */
      case Decl(mut: Mutability, x: String, e1: Expr, e2: Expr) => {
        typeInfer(env + ( x -> (mut, typ(e1)) ), e2)
      }
      /* TYPE ASSIGN (Assignment): based on whether e1 is a variable assigned to a 
       * field of an object or something else.
       */
      case Assign(e1, e2) => e1 match {
        //Ensure the proper type: field type == e1 type is extended to the environment. 
        case GetField(x1, f) => typ(e1) match {
          case t => typeInfer(env + (f -> (MConst, typ(e1))), e2)
        }
        // Fetch the variable's type from the environment. 
        case Var(x) => env.get(x) match { 
          case Some((MConst, t)) => err(typ(e1), e2) //If a constant, return error on e2. 
          //If not a constant and t equals the type of e2, run typeInfer on extend version
          //of environment with a map between mvar and the new type.
          case Some((MVar, t)) => {
            if (t == typ(e2)) { typeInfer(env + (x -> (MVar, typ(e2))), e2) } 
            else { err(typ(e1), e2) } //Throw an error if variable not in map. 
          }
          case _ => typeInfer(env + (x -> (MVar, typ(e2))), e2)
        }
        case _ => err(typ(e1), e2)
      }
       
      /* Should not match: non-source expressions or should have been removed */
      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }
  
  /*** Small-Step Interpreter ***/
  
  /* Do the operation for an inequality. */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    ((v1, v2): @unchecked) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case (N(n1), N(n2)) =>
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }
  
  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = substitute(e, esub, x)
    val ep: Expr = avoidCapture(freeVars(esub), e)
    ep match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
      case Print(e1) => Print(subst(e1))
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) esub else e
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))
      case Call(e1, args) => Call(subst(e1), args map subst)
      case Obj(fields) => Obj(fields map { case (fi,ei) => (fi, subst(ei)) })
      case GetField(e1, f) => GetField(subst(e1), f)
      case Assign(e1, e2) => Assign(subst(e1), subst(e2))
      case InterfaceDecl(tvar, t, e1) => InterfaceDecl(tvar, t, subst(e1))
        
      /*** Function Substitution (immutable parameters) ***/
      //p = func name, paramse = parameter expressions, retty = return type, e1 = func body
      //Checking on args/params: this part same as lab4
      case Function(p, Left(paramse), retty, e1) => p match {     
        //ANONYMOUS FUNCTION: 
        case None => 
          //For all params, if var name is not tuple_1, subst on e1 else return the function itself.
          val e2 = if (paramse.forall{ case(n,_) => (x!= n) } ) subst(e1) else e1
          Function(p, Left(paramse), retty, e2)	
 
        //NAMED FUNCTION:  
        case Some(a) =>
          //Same as above, but also check if x != a.
          val e2 = if (paramse.forall { case(n,_) => (x != n) } && x != a) subst(e1) else e1
          Function(p, Left(paramse), retty, e2)
      }

      /*** Function Substitution (mutable parameters) ***/            
      //Check mode and do apppropriate thing for pass by name, value and reference;
      //for paramse, need to check mode, string, type.
      case Function(p, Right(paramse@(mode, s, t)), retty, e1) => p match {    	  
    	  //ANONYMOUS FUNCTION: If unnamed function with modes, check if string x in parameters.
    	  //If not, substitute on body and return function with body e1.
    	  case None => 
    	    if (x != s) Function(p, Right(paramse), retty, subst(e1))
    	    else Function(p, Right(paramse), retty, e1)   	  

          //NAMED FUNCTION: Same as above but check equivalence with a as well.
    	  case Some(a) =>
    	    if (x != s && x != a) Function(p, Right(paramse), retty, subst(e1))
    	    Function(p, Right(paramse), retty, e1)
      }
    }
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))
    
    /*** Helpers for Call ***/
    
    def stepIfNotValue(e: Expr): Option[DoWith[Mem,Expr]] = if (isValue(e)) None else Some(step(e))
    
    /* Check whether or not the argument expression is ready to be applied. */
    def argApplyable(mode: PMode, arg: Expr): Boolean = mode match {
      case PVar => isValue(arg)
      case PName => true
      case PRef => isLValue(arg)
    }

    /*** Body ***/
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => for (m <- doget) yield { println(pretty(m, v1)); Undefined }
      case Unary(Neg, N(n1)) => doreturn( N(- n1) )
      case Unary(Not, B(b1)) => doreturn( B(! b1) )
      case Unary(Deref, a@A(_)) => doget.map( (m: Mem) => m.apply(a) )
      case Unary(Cast(e1), e2)  => if (e2 == Null) doreturn(Null) else doreturn(e2)
      case Binary(Seq, v1, e2) if isValue(v1) => doreturn( e2 )
      case Binary(Plus, S(s1), S(s2)) => doreturn( S(s1 + s2) )
      case Binary(Plus, N(n1), N(n2)) => doreturn( N(n1 + n2) )
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(inequalityVal(bop, v1, v2)) )
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(v1 == v2) )
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(v1 != v2) )
      case Binary(And, B(b1), e2) => doreturn( if (b1) e2 else B(false) )
      case Binary(Or, B(b1), e2) => doreturn( if (b1) B(true) else e2 )
      case Binary(Minus, N(n1), N(n2)) => doreturn( N(n1 - n2) )
      case Binary(Times, N(n1), N(n2)) => doreturn( N(n1 * n2) )
      case Binary(Div, N(n1), N(n2)) => doreturn( N(n1 / n2) )
      case If(B(b1), e2, e3) => doreturn( if (b1) e2 else e3 )
      
      /* DO RULE OBJ:
       *   Parameters: the fields within the object
       *   Description: allocate memory for object with param fields and then map
       *   each field of the object to an address a.
       */
      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) => 
        Mem.alloc(Obj(fields)) map { (a:A) => a:Expr }
      
      /* DO RULE GETFIELD:
       *    Parameters: memory location (address) a and field f
       *    Description: fetch data at address a of field name f.
       */
      case GetField(a @ A(_), f) => {
        //doget calls a DoWith object to which we map object address
    	doget.map( (m: Mem) => m.get(a) match { 
          //Check fields of new object to see if f exists
          case Some(Obj(fields)) => fields.get(f) match {
            case Some(field) => field
            case _ => throw StuckError(e)
          }
          //If not an object, throw error. 
          case _ => throw StuckError(e)
    	})
      }

      /* DO RULE CALL:
       *    Parameters: func name v1 and argument list args
       *    Description: address the various call cases -- no mode, pass by val,
       *    pass by name, pass by ref.
       */
      case Call(v1, args) if isValue(v1) => {
        def substfun(e1: Expr, p: Option[String]): Expr = p match {
          case None => e1
          case Some(x) => substitute(e1, v1, x)
        }
        /*** DoCall cases -- the SearchCall2, SearchCallVar and SearchCallRef  ***/
        (v1, args) match {
          /*** If No Mode ***/
          //Check if number of expected params in func == number of args in func call.
          case (Function(p, Left(params),_, e1), args) if params.length == args.length =>
            val e1p = (params, args).zipped.foldRight(e1)({
              //e1 is substitituing for each argument
              (myParams,acc)=> myParams match {
                case((name,_),value) => substitute(acc,value,name)
              }
            })
            p match {
              case None => doreturn(e1p)
              //if the function is not named, return e1p 
              case Some(x1) => doreturn(substitute(e1p,v1,x1))
              //otherwise do one more substitue on e1p, replacing its name with function itself 
            }

          //If ***Pass by Value ***
          case (Function(p, Right((PVar, x1, _)),_, e1), v2 :: Nil) if isValue(v2) =>
            //Allocate the memory for the arguments and map on 'a' evaluated to a substitute on 
            //a version of e1 dereferenced with address and the option string of function name.
            Mem.alloc(v2) map { a => substfun(substitute(e1, Unary(Deref, a), x1), p)} 

          //If ***Pass by Ref ***
          //Ensure that args are location values. 
          case (Function(p, Right((PRef, x1, _)),_, e1), lv :: Nil) if isLValue(lv) =>
            //Return a substituted function body, all instances of param name substituted with 
            //corresponding arg and option string p.
            doreturn(substfun(substitute(e1, lv, x1), p))
                  
          //If ***Pass by Name***  
          case (Function(p, Right((PName, x1, _)),_, e1), e2 :: Nil)  =>
            //Return a substituted function body, all instances of param name substituted with 
            //corresponding arg and option string p.
            doreturn(substfun(substitute(e1, e2, x1), p)) 

          /*** SearchCall Functions ***/
          case (Function(p, Right((PVar, x, _)), _, e1), e2 :: Nil) => {
            //Step on passed in arg and then map it and return a call object with v1 and e2p
            //passed a parameters.
            step(e2) map {e2p => Call(v1, e2p :: Nil)}
          }
          //exact same as above 
          case (Function(p, Right((PRef, x1, _)), _, e1), e2 :: nil) => {
            step(e2) map {e2p => Call(v1, e2p :: Nil)}
          }
         
          case _ => throw StuckError(e)
        } 
      }
      
      //decl const with name x, body v1, and continuted expression e2 subst all 
      //instances of x and e2 with body v1
      case Decl(MConst, x, v1, e2) if isValue(v1) => doreturn(substitute(e2, v1, x))
      
      //pass by value, declare new obj in memory and substute in its body 
      case Decl(MVar, x, v1, e2) if isValue(v1) =>
        Mem.alloc(v1) map { a => substitute(e2, Unary(Deref, a), x) }

      /*** DO RULE ASSIGN ***/
      case Assign(GetField(a @ A(_),f), v) if isValue(v) => {
        for (_ <- domodify { (m: Mem) => { 
            //If mem contains stored address of the field, get the memory at that 
            //specific address for the object.
            if (m.contains(a)) {   
              val obj = m(a) 
              val newobj = obj match {
                //Make a new obj with with the fields of new field f mapped to v,
                //the value.
                case Obj(fields) => Obj( fields + (f -> (v))) 
                case _ => throw StuckError(e) //If no fields, throw an error.
                }
                //Add to memory m with address to object.
                m + (a -> newobj) 
            } 
            else m //Otherwise, return memory.
          }
        }) yield v
      }

      /*** DO RULE ASSIGN VAR ***/
      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) => {
        //Modify the memroy and we add a mapping from the address to the value 
        //and store it to memory.
        for (_ <- domodify { (m: Mem) => (m.+(a, v)): Mem }) yield v
      }
          
      /* Base Cases: Error Rules */
      /*** Fill-in cases here. ***/
        
      /* Inductive Cases: Search Rules */
      case Print(e1) =>
        //Same as step(e1).map{ e1p => Print(e1p) }
        for (e1p <- step(e1)) yield Print(e1p)
      case Unary(uop, e1) =>
        for (e1p <- step(e1)) yield Unary(uop, e1p)
      case Binary(bop, v1, e2) if isValue(v1) =>
        for (e2p <- step(e2)) yield Binary(bop, v1, e2p)
      case Binary(bop, e1, e2) =>
        for (e1p <- step(e1)) yield Binary(bop, e1p, e2)
      case If(e1, e2, e3) =>
        for (e1p <- step(e1)) yield If(e1p, e2, e3)
      case Obj(fields) => fields find { case (_, ei) => !isValue(ei) } match {
        case Some((fi,ei)) =>
       	  for (eip <- step(ei)) yield Obj(fields + (fi -> eip))
    	case None => throw StuckError(e)
      }	 
      case GetField(e1, f) => {
    	if(e1 == Null) throw new NullDereferenceError(e1)
    	for (e1p <- step(e1)) yield GetField(e1p, f);
      } 
      /*** More Search cases here. ***/
      case Decl(mut, x, e1, e2) => for (e1p <- step(e1)) yield Decl(mut, x, e1p, e2)
      case Call(e1, e2) => for (e1p <- step(e1)) yield Call(e1p, e2) //e1 isnt
      case Assign(e1, e2) if isLValue(e1) && !isValue(e2)=> {
        for (e2p <- step(e2)) yield Assign(e1, e2p) //if e2 isn't a value and we need to step on it
      }
      case Assign(e1, e2) => for (e1p <- step(e1)) yield Assign(e1p, e2) //if !isValue(e1)
      case _ => throw StuckError(e) // Everything else is a stuck error.
    }
  }

  /*** External Interfaces ***/

  this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(500) // comment this out or set to None to not bound the number of steps.
  
  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  
  case class TerminationError(e: Expr) extends Exception {
    override def toString = Parser.formatErrorMessage(e.pos, "TerminationError", "run out of steps in evaluating " + e)
  }
  
  def iterateStep(e: Expr): Expr = {
    require(closed(e), "not a closed expression: free variables: %s".format(freeVars(e)) )
    def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
      if (Some(n) == maxSteps) throw TerminationError(e)
      else if (isValue(e)) doreturn( e )
      else {
        for {
          m <- doget[Mem]
          _ = if (debug) { println("Step %s:%n  %s%n  %s".format(n, m, e)) }
          ep <- step(e)
          epp <- loop(ep, n + 1)
        } yield
        epp
      }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val (m,v) = loop(e, 0)(Mem.empty)
    if (debug) {
      println("Result:%n  %s%n  %s".format(m,v))
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(removeInterfaceDecl(jsy.lab5.Parser.parse(s)))
  
  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        jsy.lab5.Parser.parseFile(file)
      }} getOrElse {
        return
      }
      
    val exprlowered =
      handle(None: Option[Expr]) {Some{
        removeInterfaceDecl(expr)
      }} getOrElse {
        return
      }  
    
    handle() {
      val t = inferType(exprlowered)
    }
    
    handle() {
      val v1 = iterateStep(exprlowered)
      println(pretty(v1))
    }
  }
    
}