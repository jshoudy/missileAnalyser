package ch.ethz.sae;

import java.security.interfaces.DSAKey;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import apron.Abstract1;
import apron.ApronException;
import apron.Coeff;
import apron.Environment;
import apron.Interval;
import apron.Lincons1;
import apron.Linexpr1;
import apron.Linterm1;
import apron.Manager;
import apron.MpqScalar;
import apron.Polka;
import apron.Scalar;
import apron.Texpr1BinNode;
import apron.Texpr1CstNode;
import apron.Texpr1Intern;
import apron.Texpr1Node;
import apron.Texpr1VarNode;
import soot.IntegerType;
import soot.Local;
import soot.RefType;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.BinopExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.Expr;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.internal.AbstractBinopExpr;
import soot.jimple.internal.JAddExpr;
import soot.jimple.internal.JDivExpr;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JGeExpr;
import soot.jimple.internal.JGtExpr;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JLeExpr;
import soot.jimple.internal.JLtExpr;
import soot.jimple.internal.JMulExpr;
import soot.jimple.internal.JNeExpr;
import soot.jimple.internal.JSubExpr;
import soot.jimple.internal.JimpleLocal;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardBranchedFlowAnalysis;
import soot.util.Chain;

// Implement your numerical analysis here.
public class Analysis extends ForwardBranchedFlowAnalysis<AWrapper> {

	private void recordIntLocalVars() {

		Chain<Local> locals = g.getBody().getLocals();
		
		int count = 0;
		Iterator<Local> it = locals.iterator();
		while (it.hasNext()) {
			JimpleLocal next = (JimpleLocal) it.next();
			// String name = next.getName();
			if (next.getType() instanceof IntegerType)
				count += 1;
		}

		local_ints = new String[count];

		int i = 0;
		it = locals.iterator();
		while (it.hasNext()) {
			JimpleLocal next = (JimpleLocal) it.next();
			String name = next.getName();
			if (next.getType() instanceof IntegerType)
				local_ints[i++] = name;
		}
	}

	/* Build an environment with integer variables. */
	public void buildEnvironment() {

		recordIntLocalVars();

		String ints[] = new String[local_ints.length];

		/* add local ints */
		for (int i = 0; i < local_ints.length; i++) {
			ints[i] = local_ints[i];
		}

		env = new Environment(ints, reals);
	}

	/* Instantiate a domain. */
	private void instantiateDomain() {
		// Initialize variable 'man' to Polyhedra
		man = new Polka(true);
	}

	/* === Constructor === */
	public Analysis(UnitGraph g, SootClass jc) {
		super(g);

		this.g = g;
		this.jclass = jc;
		this.constructorCalls = new HashMap<String, List<Value>>();
		
		buildEnvironment();
		instantiateDomain();
		sprint("successfully constructed " + jc);

	}

	void run() {
		sprint("called run");
		doAnalysis();
	}

	// call this if you encounter statement/expression which you should not be handling
	static void unhandled(String what) {
		System.err.println("Can't handle " + what);
		System.exit(1);
	}

	// handle conditionals
	private void handleIf(AbstractBinopExpr expr, Abstract1 in, AWrapper ow,
			AWrapper ow_branchout) throws ApronException {
		ident++;

		Value left = expr.getOp1();
		Value right = expr.getOp2();

		sprint("called handleIf with expr: " + expr.toString());

		Lincons1 fallthrough = null;
		Lincons1 branchout = null;

		// handles eq expr
		if(expr instanceof JEqExpr){
			JEqExpr j = new JEqExpr(left,right);
			if(left instanceof IntConstant){
				if(right instanceof IntConstant){
					// should never reach this block
					sprint("eq expr with int int");
				} else if(right instanceof JimpleLocal){
					sprint("eq expr with int local");
					String var = right.toString();

					IntConstant c = ((IntConstant) left);
					Linterm1 term = new Linterm1(var,new MpqScalar(1));
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{term},new MpqScalar(-1*c.value));

					//expression ex: for 5==x -> 5-x<>0
					fallthrough = new Lincons1(Lincons1.DISEQ,exp);
					//expression ex: for 5==x -> x-5=0
					branchout = new Lincons1(Lincons1.EQ,exp);
					printGraph();
				} else {
					unhandled("eq expression with right of type: " + right.getType().toString());
				}
			} else if(left instanceof JimpleLocal){
				if(right instanceof IntConstant){
					sprint("eq expr with local int");
					String var = left.toString();

					IntConstant c = ((IntConstant) right);
					Linterm1 term = new Linterm1(var,new MpqScalar(1));
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{term},new MpqScalar(-1*c.value));

					//expression ex: for x==5 -> x-5<>0
					fallthrough = new Lincons1(Lincons1.EQ,exp);
					//expression ex: for x==5 -> x-5=0
					branchout = new Lincons1(Lincons1.DISEQ,exp);
				} else if(right instanceof JimpleLocal){
					sprint("eq expr with local local");
					String varl = left.toString();
					String varr = right.toString();

					Linterm1 terml = new Linterm1(varl,new MpqScalar(1));
					Linterm1 termr = new Linterm1(varr,new MpqScalar(-1));
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{terml, termr},new MpqScalar(0));

					//expression ex: for x==q -> x-q<>0
					fallthrough = new Lincons1(Lincons1.EQ,exp);
					//expression ex: for x==q -> x-q=0
					branchout = new Lincons1(Lincons1.DISEQ,exp);
				} else {
					unhandled("eq expression with right of type: " + right.getType().toString());
				}
			} else {
				unhandled("eq expression with left of type: " + left.getType().toString());
			}

			//handles gte expr
		} else if(expr instanceof JGeExpr){
			JGeExpr j = new JGeExpr(left,right);

			if(left instanceof IntConstant){
				if(right instanceof IntConstant){
					// should never reach this block
					sprint("gte expr with int int");
				} else if(right instanceof JimpleLocal){
					sprint("gte expr with int local");
					String var = right.toString();

					IntConstant c = ((IntConstant) left);
					Linterm1 term1 = new Linterm1(var,new MpqScalar(-1));
					Linterm1 term2 = new Linterm1(var,new MpqScalar(1));
					Linexpr1 exp1 = new Linexpr1(env,new Linterm1[]{term1},new MpqScalar(c.value));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{term2},new MpqScalar(-1*c.value));

					//expression ex: 5>=x -> x-5>0
					fallthrough = new Lincons1(Lincons1.SUP,exp2);
					//expression ex: 5>=x -> 5-x>=0
					branchout = new Lincons1(Lincons1.SUPEQ,exp1);
				} else {
					unhandled("ge expression with right of type: " + right.getType().toString());
				}
			} else if(left instanceof JimpleLocal){
				if(right instanceof IntConstant){
					sprint("gte expr with local int");
					String var = left.toString();

					IntConstant c = ((IntConstant) right);
					Linterm1 term1 = new Linterm1(var,new MpqScalar(1));
					Linterm1 term2 = new Linterm1(var,new MpqScalar(-1));
					Linexpr1 exp1 = new Linexpr1(env,new Linterm1[]{term1},new MpqScalar(-1*c.value));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{term2},new MpqScalar(c.value));

					//expression ex: x>=5 -> 5-x>0
					fallthrough = new Lincons1(Lincons1.SUP,exp2);
					//expression ex: x>=5 -> x-5>=0
					branchout = new Lincons1(Lincons1.SUPEQ,exp1);
				} else if(right instanceof JimpleLocal){
					sprint("gte expr with local local");
					String varl = left.toString();
					String varr = right.toString();

					Linterm1 terml1 = new Linterm1(varl,new MpqScalar(1));
					Linterm1 termr1 = new Linterm1(varr,new MpqScalar(-1));
					Linterm1 terml2 = new Linterm1(varl,new MpqScalar(-1));
					Linterm1 termr2 = new Linterm1(varr,new MpqScalar(1));
					Linexpr1 exp1 = new Linexpr1(env,new Linterm1[]{terml1,termr1},new MpqScalar(0));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{terml2,termr2},new MpqScalar(0));

					//expression ex: x>=q -> q-x>0
					fallthrough = new Lincons1(Lincons1.SUP,exp2);
					//expression ex: x>=q -> x-q>=0
					branchout = new Lincons1(Lincons1.SUPEQ,exp1);
				} else {
					unhandled("ge expression with right of type: " + right.getType().toString());
				}
			} else {
				unhandled("ge expression with left of type: " + left.getType().toString());
			}

			//handles gt expr
		} else if(expr instanceof JGtExpr){
			JGtExpr j = new JGtExpr(left,right);

			if(left instanceof IntConstant){
				if(right instanceof IntConstant){
					// should never reach this block
					sprint("gt expr with int int");
				} else if(right instanceof JimpleLocal){
					sprint("gt expr with int local");
					String var = right.toString();

					IntConstant c = ((IntConstant) left);
					Linterm1 term1 = new Linterm1(var,new MpqScalar(1));
					Linterm1 term2 = new Linterm1(var,new MpqScalar(-1));
					Linexpr1 exp1 = new Linexpr1(env,new Linterm1[]{term1},new MpqScalar(-1*c.value));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{term2},new MpqScalar(c.value));

					//expression ex: 5>x -> x-5>=0
					fallthrough = new Lincons1(Lincons1.SUPEQ,exp1);
					//expression ex: 5>x -> 5-x>0
					branchout = new Lincons1(Lincons1.SUP,exp2);
				} else {
					unhandled("gt expression with right of type: " + right.getType().toString());
				}
			} else if(left instanceof JimpleLocal){
				if(right instanceof IntConstant){
					sprint("gt expr with local int");
					String var = left.toString();

					IntConstant c = ((IntConstant) right);
					Linterm1 term1 = new Linterm1(var,new MpqScalar(1));
					Linterm1 term2 = new Linterm1(var,new MpqScalar(-1));
					Linexpr1 exp1 = new Linexpr1(env,new Linterm1[]{term1},new MpqScalar(-1*c.value));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{term2},new MpqScalar(c.value));

					//expression ex: x>5 -> 5-x>=0
					fallthrough = new Lincons1(Lincons1.SUPEQ,exp2);
					//expression ex: x>5 -> x-5>0
					branchout = new Lincons1(Lincons1.SUP,exp1);
				} else if(right instanceof JimpleLocal){
					sprint("gt expr with local local");
					String varl = left.toString();
					String varr = right.toString();

					Linterm1 terml1 = new Linterm1(varl,new MpqScalar(1));
					Linterm1 termr1 = new Linterm1(varr,new MpqScalar(-1));
					Linterm1 terml2 = new Linterm1(varl,new MpqScalar(-1));
					Linterm1 termr2 = new Linterm1(varr,new MpqScalar(1));
					Linexpr1 exp1 = new Linexpr1(env,new Linterm1[]{terml1,termr1},new MpqScalar(0));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{terml2,termr2},new MpqScalar(0));

					//expression ex: x>q -> q-x>=0
					fallthrough = new Lincons1(Lincons1.SUPEQ,exp2);
					//expression ex: x>q -> x-q>0
					branchout = new Lincons1(Lincons1.SUP,exp1);
				} else {
					unhandled("gt expression with right of type: " + right.getType().toString());
				}
			} else {
				unhandled("gt expression with left of type: " + left.getType().toString());
			}

			//handles lte expr
		} else if(expr instanceof JLeExpr){
			JLeExpr j = new JLeExpr(left,right);

			if(left instanceof IntConstant){
				if(right instanceof IntConstant){
					// should never reach this block
					sprint("lte expr with int int");
				} else if(right instanceof JimpleLocal){
					sprint("lte expr with int local");
					String var = right.toString();

					IntConstant c = ((IntConstant) left);
					Linterm1 term1 = new Linterm1(var,new MpqScalar(1));
					Linterm1 term2 = new Linterm1(var,new MpqScalar(-1));
					Linexpr1 exp1 = new Linexpr1(env,new Linterm1[]{term1},new MpqScalar(-1*c.value));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{term2},new MpqScalar(c.value));

					//expression ex: 5<=x -> 5-x>0
					fallthrough = new Lincons1(Lincons1.SUP,exp2);
					//expression ex: 5<=x -> x-5>=0
					branchout = new Lincons1(Lincons1.SUPEQ,exp1);

				} else {
					unhandled("le expression with right of type: " + right.getType().toString());
				}
			} else if(left instanceof JimpleLocal){
				if(right instanceof IntConstant){
					sprint("lte expr with local int");
					String var = left.toString();

					IntConstant c = ((IntConstant) right);
					Linterm1 term1 = new Linterm1(var,new MpqScalar(-1));
					Linterm1 term2 = new Linterm1(var,new MpqScalar(1));
					Linexpr1 exp1 = new Linexpr1(env,new Linterm1[]{term1},new MpqScalar(c.value));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{term2},new MpqScalar(-1*c.value));

					//expression ex: x<=5 -> x-5>0
					fallthrough = new Lincons1(Lincons1.SUP,exp2);
					//expression ex: x<=5 -> 5-x>=0
					branchout = new Lincons1(Lincons1.SUPEQ,exp1);

				} else if(right instanceof JimpleLocal){
					sprint("lte expr with local local");
					String varl = left.toString();
					String varr = right.toString();

					Linterm1 terml1 = new Linterm1(varl,new MpqScalar(-1));
					Linterm1 termr1 = new Linterm1(varr,new MpqScalar(1));
					Linterm1 terml2 = new Linterm1(varl,new MpqScalar(1));
					Linterm1 termr2 = new Linterm1(varr,new MpqScalar(-1));
					Linexpr1 exp1 = new Linexpr1(env,new Linterm1[]{terml1,termr1},new MpqScalar(0));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{terml2,termr2},new MpqScalar(0));

					//expression ex: x<=q -> x-q>0
					fallthrough = new Lincons1(Lincons1.SUP,exp2);
					//expression ex: x<=q -> q-x>=0
					branchout = new Lincons1(Lincons1.SUPEQ,exp1);

				} else {
					unhandled("le expression with right of type: " + right.getType().toString());
				}
			} else {
				unhandled("le expression with left of type: " + left.getType().toString());
			}

			//handle lt expr
		} else if(expr instanceof JLtExpr){
			JLtExpr j = new JLtExpr(left,right);

			if(left instanceof IntConstant){
				if(right instanceof IntConstant){
					// should never reach this block
					sprint("lt expr with int int");
				} else if(right instanceof JimpleLocal){
					sprint("lt expr with int local");
					String var = right.toString();

					IntConstant c = ((IntConstant) left);
					Linterm1 term1 = new Linterm1(var,new MpqScalar(1));
					Linterm1 term2 = new Linterm1(var,new MpqScalar(-1));
					Linexpr1 exp1 = new Linexpr1(env,new Linterm1[]{term1},new MpqScalar(-1*c.value));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{term2},new MpqScalar(c.value));

					//expression ex: 5<x -> 5-x>=0
					fallthrough = new Lincons1(Lincons1.SUPEQ,exp2);
					//expression ex: 5<x -> x-5>0
					branchout = new Lincons1(Lincons1.SUP,exp1);

				} else {
					unhandled("lt expression with right of type: " + right.getType().toString());
				}
			} else if(left instanceof JimpleLocal){
				if(right instanceof IntConstant){
					sprint("lt expr with local int");
					String var = left.toString();

					IntConstant c = ((IntConstant) right);
					Linterm1 term1 = new Linterm1(var,new MpqScalar(-1));
					Linterm1 term2 = new Linterm1(var,new MpqScalar(1));
					Linexpr1 exp1 = new Linexpr1(env,new Linterm1[]{term1},new MpqScalar(c.value));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{term2},new MpqScalar(-1*c.value));

					//expression x<5 -> x-5>=0
					fallthrough = new Lincons1(Lincons1.SUPEQ,exp2);
					//expression ex: x<5 -> 5-x>0
					branchout = new Lincons1(Lincons1.SUP,exp1);

				} else if(right instanceof JimpleLocal){
					sprint("gt expr with local local");
					String varl = left.toString();
					String varr = right.toString();

					Linterm1 terml1 = new Linterm1(varl,new MpqScalar(-1));
					Linterm1 termr1 = new Linterm1(varr,new MpqScalar(1));
					Linterm1 terml2 = new Linterm1(varl,new MpqScalar(1));
					Linterm1 termr2 = new Linterm1(varr,new MpqScalar(-1));
					Linexpr1 exp1 = new Linexpr1(env,new Linterm1[]{terml1,termr1},new MpqScalar(0));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{terml2,termr2},new MpqScalar(0));

					//expression ex: x<q -> x-q>=0
					fallthrough = new Lincons1(Lincons1.SUPEQ,exp2);
					//expression ex: x<q -> q-x>0
					branchout = new Lincons1(Lincons1.SUP,exp1);
					

				} else {
					unhandled("lt expression with right of type: " + right.getType().toString());
				}
			} else {
				unhandled("lt expression with left of type: " + left.getType().toString());
			}

			//handles ne expression
		} else if(expr instanceof JNeExpr){
			JNeExpr j = new JNeExpr(left,right);
			if(left instanceof IntConstant){
				if(right instanceof IntConstant){
					// should never reach this block
					sprint("ne expr with int int");
				} else if(right instanceof JimpleLocal){
					sprint("ne expr with int local");
					String var = right.toString();

					IntConstant c = ((IntConstant) left);
					Linterm1 term = new Linterm1(var,new MpqScalar(1));
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{term},new MpqScalar(-1*(c.value)));

					//expression ex: for 5==x -> x-5=0
					fallthrough = new Lincons1(Lincons1.EQ,exp);
					//expression ex: for 5!=x -> x-5<>0
					branchout = new Lincons1(Lincons1.DISEQ,exp);

				} else {
					unhandled("eq expression with right of type: " + right.getType().toString());
				}
			} else if(left instanceof JimpleLocal){
				if(right instanceof IntConstant){
					sprint("eq expr with local int");
					String var = left.toString();

					IntConstant c = ((IntConstant) right);
					Linterm1 term = new Linterm1(var,new MpqScalar(1));
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{term},new MpqScalar(-1*(c.value)));

					//expression ex: for x!=5 -> x-5=0
					fallthrough = new Lincons1(Lincons1.EQ,exp);
					//expression ex: for x!=5 -> x-5<>0
					branchout = new Lincons1(Lincons1.DISEQ,exp);

				} else if(right instanceof JimpleLocal){
					sprint("eq expr with local local");
					String varl = left.toString();
					String varr = right.toString();

					Linterm1 terml = new Linterm1(varl,new MpqScalar(1));
					Linterm1 termr = new Linterm1(varr,new MpqScalar(-1));
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{terml, termr},new MpqScalar(0));

					//expression ex: for x==q -> q-x=0
					fallthrough = new Lincons1(Lincons1.EQ,exp);
					//expression ex: for x!=q -> x-q<>0
					branchout = new Lincons1(Lincons1.DISEQ,exp);

				} else {
					unhandled("eq expression with right of type: " + right.getType().toString());
				}
			} else {
				unhandled("eq expression with left of type: " + left.getType().toString());
			}
			//not handled case
		} else {
			unhandled("expr of type 1 " + expr.getType());
		}
		sprint("fallthrough: " + fallthrough.toString());
		sprint("branchout: " + branchout.toString());

		ow.get().meet(man, fallthrough);
		ow_branchout.get().meet(man, branchout);

		ident--;
	}
	// handle assignments
	private void handleDef(Abstract1 o, Value left, Value right)
			throws ApronException {
		ident++;
		
		sprint("handleDef called with " + 
				last(right.getClass().toString()) + ": "
				+ left + " = " + right);
		
		Texpr1Node lAr = null;
		Texpr1Node rAr = null;
		Texpr1Intern xp = null;

		if (left instanceof JimpleLocal) {
			ident++;
			String varName = ((JimpleLocal) left).getName();
			//sprint("varName = " + varName);
			
			if (right instanceof IntConstant) {
				//sprint("Entering IntConstant");
				/* Example of handling assignment to an integer constant */
				IntConstant c = ((IntConstant) right);

				rAr = new Texpr1CstNode(new MpqScalar(c.value)); 
				xp = new Texpr1Intern(env, rAr);

				sprint("    Assigning IntConstant of value " + c.value);
				o.assign(man, varName, xp, null);
				
				
			} else if (right instanceof JimpleLocal) {
				
				
				sprint("Entering JimpleLocal");
				String name = ((JimpleLocal) right).getName();
				List<Value> constructorCall = constructorCalls.get(name);
				if(constructorCall != null){
					constructorCalls.put(varName, constructorCall);
				}
				
				/* Example of handling assignment to a local variable */
				if (env.hasVar(name)){
					rAr = new Texpr1VarNode(name);
					xp = new Texpr1Intern(env, rAr);
					
					sprint("Assigning JimpleLocal with name " + name);
					o.assign(man, varName, xp, null);
				}else{
					sprint("env.hasVar("+name+") is false");
				}
				
				
			} else if (right instanceof NewExpr){
				sprint("Entering NewExpr");
				NewExpr newExpr = (NewExpr)right;
				sprint("SKIPING: Assigning newObject of type " + right + " to " + varName);
			} else if (right instanceof BinopExpr) {
				sprint("Entering BinopExpr");
				BinopExpr b = (BinopExpr) right;
				Value l = (Value) b.getOp1();
				Value r = (Value) b.getOp2();
				
				if(l instanceof IntConstant){
					IntConstant c = ((IntConstant) l);
					lAr = new Texpr1CstNode(new MpqScalar(c.value));
				} else if(l instanceof JimpleLocal){
					String name = ((JimpleLocal) l).getName();
					if (env.hasVar(name)){
						lAr = new Texpr1VarNode(name);
					}else{
						sprint("env.hasVar("+name+") is false");
					}
				} else {
					unhandled("left value of binary operator " + l.getType());
				}
				
				if(r instanceof IntConstant){
					IntConstant c = ((IntConstant) r);
					rAr = new Texpr1CstNode(new MpqScalar(c.value));
				} else if(r instanceof JimpleLocal){
					String name = ((JimpleLocal) r).getName();
					if (env.hasVar(name)){
						rAr = new Texpr1VarNode(name);
					}else{
						sprint("env.hasVar("+name+") is false");
					}
				} else {
					unhandled("right value of binary operator " + r.getType());
				}
				
				int opp = 0;
				
				if(right instanceof JMulExpr){
					opp = Texpr1BinNode.OP_MUL;
				} else if(right instanceof JSubExpr){
					opp = Texpr1BinNode.OP_SUB;
				} else if(right instanceof JAddExpr){
					opp = Texpr1BinNode.OP_ADD;
				} else if(right instanceof JDivExpr){
					opp = Texpr1BinNode.OP_DIV;
				} else {
					unhandled("expr of type 2 " + right.getType());
				}
				
				Texpr1BinNode bin = new Texpr1BinNode(opp,lAr,rAr);
				xp = new Texpr1Intern(env,bin);
				sprint("Assigning BinopExpr of value " + bin.toString());
				o.assign(man, varName, xp, null);
				
			} else if (right instanceof ThisRef){
				sprint("We are in a method in class " + right.getType());
			} else {
				unhandled(" (in handleDef) right of type '" + right + "' ("+ right.getClass() + ")");
			}
			ident--;
		}
		ident--;
	}

	@Override
	protected void flowThrough(AWrapper current, Unit op,
			List<AWrapper> fallOut, List<AWrapper> branchOuts) {
		ident++;
		Stmt s = (Stmt) op;
		
		try {
			
			Abstract1 in = current.get();
			Abstract1 out = new Abstract1(man, in);
			Abstract1 out_branchout = new Abstract1(man, in);
			AWrapper out_wrapper = new AWrapper(out);
			AWrapper out_branchout_wrapper = new AWrapper(out_branchout);	
			
			sprint("flowThrough called with " + last(s.getClass().toString()) + ", in: " + current);

			if (s instanceof DefinitionStmt) {
				// call handleDef
				Value left = ((DefinitionStmt) s).getLeftOp();
				Value right = ((DefinitionStmt) s).getRightOp();
				handleDef(out,left,right);
			} else if (s instanceof JIfStmt) {
				// call handleIf
				AbstractBinopExpr cond = (AbstractBinopExpr) ((JIfStmt) s).getCondition();
				sprint("condition: " + cond.toString());
				handleIf(cond,in, out_wrapper, out_branchout_wrapper);
				
			} else if (s instanceof InvokeStmt){
				// call handleInvoke
				InvokeStmt stmt = (InvokeStmt)s;
				handleMethodInvoke(out, stmt);
			} else  {
				sprint("Unhandled operation: " + last(s.getClass().toString()));
			}
			
			// add output to fallOut 
			{
				AWrapper out_final_wrapper = new AWrapper(out);
		        Iterator<AWrapper> it = fallOut.iterator();
		        while (it.hasNext()) {
		                copy(out_final_wrapper, it.next());
		        }
				//fallOut.add(out_final_wrapper);
			}
			// add branched output to branchOuts 
			{
				AWrapper out_final_branchout_wrapper = new AWrapper(out_branchout);
		        Iterator<AWrapper> it = branchOuts.iterator();
		        while (it.hasNext()) {
		                copy(out_final_branchout_wrapper, it.next());
		        }
				//branchOuts.add(out_final_branchout_wrapper);
			}
			sprint("fallOut = " + fallOut);
			sprint("branchOuts = " + branchOuts);
			
		} catch (ApronException e) {
			// TODO Auto-generated catch block
			sprint("reached catch block in flowThrough");
			e.printStackTrace();
		}
		ident--;
	}

	private void handleMethodInvoke(Abstract1 o, InvokeStmt s) throws ApronException {
		ident++;
		sprint("Entering handleInvoke " + s);
		InstanceInvokeExpr expr = (InstanceInvokeExpr)s.getInvokeExpr();
		
		if(expr instanceof SpecialInvokeExpr)
		if(((SpecialInvokeExpr)expr).getMethodRef().name().equals("<init>"))
		{
			// This is constructor call
			SpecialInvokeExpr initExpr = (SpecialInvokeExpr)expr;
			JimpleLocal base = (JimpleLocal)initExpr.getBase();
			sprint("Constructor call on "+ ((RefType)(base.getType())) +"!");
			
			for(Value v : initExpr.getArgs()){
				sprint("  * Got argument: " + v);
			}
			sprint("Adding arguments (count: " + initExpr.getArgCount() + ") to this.constructorCalls with key: " + base);
			constructorCalls.put(base.getName(), initExpr.getArgs());
			return;
		}
		
		// Normal method call
		SootMethodRef method = expr.getMethodRef();
		String className = method.declaringClass().getName();
		JimpleLocal base = (JimpleLocal)expr.getBase();
		if(method.name().equals("fire") && className.equals("MissileBattery")){
			ident++;
			
			handleMissileBatteryFire(base, expr, o);

			ident--;
		}
		
		ident--;
	}
	
	private void handleMissileBatteryFire(JimpleLocal base, InstanceInvokeExpr expr, Abstract1 o) throws ApronException{
		sprint("Entering MissileBattery.fire(int)");
		if(o.isBottom(man)){
			sprint("Is bottom! This will never be called.. soo, return!");
			return;
		}

		int sizeOfBattery = ((IntConstant)this.constructorCalls.get(base.getName()).get(0)).value;
		Interval sizeOfBatteryInterval = new Interval(0, sizeOfBattery - 1);
		
		Interval missileIdxInterval = getInterval(expr.getArg(0), o);
		sprint("missileIdxInterval = " + missileIdxInterval);
		sprint("Checking that " + missileIdxInterval + " is a subset of " + sizeOfBatteryInterval);
		if(missileIdxInterval.cmp(sizeOfBatteryInterval) > 0){
			sprint("** UNSAFE!! "+missileIdxInterval+" (missile index) is not subset of " + sizeOfBatteryInterval + " (size)");
			isSafe = false;
		}else{
			sprint("OK:)");
		}
	}

	// Initialize starting label (top)
	@Override
	protected AWrapper entryInitialFlow() {
		ident++;
		//sprint("called entryIntitialFlow");
		Abstract1 top = null;
		try {
			top = new Abstract1(man,env);
			//sprint(top.toString());
		} catch (ApronException e) {
			// TODO Auto-generated catch block
			sprint("reached catch block of entryInitialFlow");
			e.printStackTrace();
		}
		ident--;	
		return new AWrapper(top);
	}

	// Implement Join
	@Override
	protected void merge(AWrapper src1, AWrapper src2, AWrapper trg) {
		ident++;
		sprint("merge called with src1: " + src1.toString());
		sprint("                  src2: " + src2.toString());
		sprint("                  trg: " + trg.toString());
		try {
			trg.set(src1.get().joinCopy(man, src2.get()));
		} catch (ApronException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		ident--;
	}

	// Initialize all labels (bottom)
	@Override
	protected AWrapper newInitialFlow() {
		ident++;
		//sprint("called newInitialFlow");
		Abstract1 bot = null;
		try {
			bot = new Abstract1(man,env,true);
			//sprint(bot.toString());
		} catch (ApronException e) {
			// TODO Auto-generated catch block
			sprint("reached catch block in newInitialFlow");
			e.printStackTrace();
		}
		ident--;
		return new AWrapper(bot);	
	}

	@Override
	protected void copy(AWrapper source, AWrapper dest) {
		//sprint("called copy");
		dest.copy(source);
		//sprint("finished copy");
	}

	/* It may be useful for widening */
	/*
	 * private HashSet<Stmt> backJumps = new HashSet<Stmt>(); private
	 * HashSet<Integer> backJumpIntervals = new HashSet<Integer>();
	 */

	public static Manager man;
	private Environment env;
	public UnitGraph g;
	public String local_ints[]; // integer local variables of the method
	public static String reals[] = { "foo" };
	public SootClass jclass;
	private int ident = 0;
	private HashMap<String, List<Value>> constructorCalls;
	
	public boolean isSafe = true;
	
	private Interval getInterval(Value v, Abstract1 o) throws ApronException{
		if(v instanceof Interval){
			return (Interval)v;
		}
		
		if(v instanceof IntConstant){
			IntConstant i = (IntConstant)v;
			return new Interval(i.value, i.value);
		}
		
		if(v instanceof JimpleLocal){
			JimpleLocal local = (JimpleLocal)v;
			return o.getBound(man, local.getName());
		}
		
		unhandled("(getInterval) when v is type of " + v.getClass());
		return null;
	}
	
	public String last(String s){
		return s.substring(s.lastIndexOf(".")+1);
	}
	
	public void sprint(String what){
		for (int i = 0; i < this.ident; i++){
			System.out.print("  ");
		}
		System.out.println(what);
	}
	
	public void printGraph(){
		System.out.println(g.getBody().toString());
	}
}
