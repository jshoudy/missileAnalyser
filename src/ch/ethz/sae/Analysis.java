package ch.ethz.sae;

import gmp.Mpq;

import java.security.interfaces.DSAKey;
import java.util.ArrayList;
import java.util.Dictionary;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import apron.Abstract0;
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
import soot.JastAddJ.IfStmt;
import soot.dava.internal.AST.ASTTryNode.container;
import soot.jimple.AddExpr;
import soot.jimple.BinopExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.Expr;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.NumericConstant;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.internal.AbstractBinopExpr;
import soot.jimple.internal.JAddExpr;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JDivExpr;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JGeExpr;
import soot.jimple.internal.JGotoStmt;
import soot.jimple.internal.JGtExpr;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JLeExpr;
import soot.jimple.internal.JLtExpr;
import soot.jimple.internal.JMulExpr;
import soot.jimple.internal.JNeExpr;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JReturnVoidStmt;
import soot.jimple.internal.JSubExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.annotation.logic.Loop;
import soot.jimple.toolkits.annotation.logic.LoopFinder;
import soot.tagkit.IntegerConstantValueTag;
import soot.toolkits.graph.LoopNestTree;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardBranchedFlowAnalysis;
import soot.util.Chain;
import soot.util.Switch;

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
		this.previousFires = new HashMap<String, List<Interval>>();
		this.missileBatteryAssignments = new HashMap<String, String>();
		buildEnvironment();
		instantiateDomain();
		

		LoopNestTree loops = new LoopNestTree(g.getBody());
		for (Loop l : loops) {
			Stmt h = l.getHead();
			backJumps.put(h,new Tuple<Integer, List<Stmt>>(new Integer(0), l.getLoopStatements()));
			
		}
		
		
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

		Lincons1 not_if1 = null,
				 not_if2 = null,
				 into_if1 = null,
				 into_if2 = null;
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
					Linterm1 term2 = new Linterm1(var,new MpqScalar(-1));
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{term},new MpqScalar(-1*c.value));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{term2},new MpqScalar(1*c.value));
					//expression ex: for 5==x -> 5-x != 0, 5-x < 0 && 5-x > 0 
					
					not_if1 = new Lincons1(Lincons1.SUP, exp);
					not_if2 = new Lincons1(Lincons1.SUP, exp2);
					
					//expression ex: for 5==x -> x-5=0
					into_if1 = new Lincons1(Lincons1.EQ,exp);
				} else {
					unhandled("eq expression with right of type: " + right.getType().toString());
				}
			} else if(left instanceof JimpleLocal){
				if(right instanceof IntConstant){
					sprint("eq expr with local int");
					String var = left.toString();

					IntConstant c = ((IntConstant) right);
					Linterm1 term = new Linterm1(var,new MpqScalar(1));
					Linterm1 term2 = new Linterm1(var,new MpqScalar(-1));
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{term},new MpqScalar(-1*c.value));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{term2},new MpqScalar(1*c.value));

					//expression ex: for x==5 -> x-5<>0
					not_if1 = new Lincons1(Lincons1.SUP,exp);
					not_if2 = new Lincons1(Lincons1.SUP, exp2);
					
					//expression ex: for x==5 -> x-5=0
					into_if1 = new Lincons1(Lincons1.EQ,exp);
				} else if(right instanceof JimpleLocal){
					sprint("eq expr with local local");
					String varl = left.toString();
					String varr = right.toString();

					Linterm1 terml = new Linterm1(varl,new MpqScalar(1));
					Linterm1 termr = new Linterm1(varr,new MpqScalar(-1));
					Linterm1 terml2 = new Linterm1(varl,new MpqScalar(-1));
					Linterm1 termr2 = new Linterm1(varr,new MpqScalar(1));
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{terml, termr},new MpqScalar(0));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{termr2, terml2},new MpqScalar(0));

					//expression ex: for x==q -> x-q<>0
					not_if1 = new Lincons1(Lincons1.SUP,exp);
					not_if2 = new Lincons1(Lincons1.SUP, exp2);
					
					//expression ex: for x==q -> x-q=0
					into_if1 = new Lincons1(Lincons1.EQ,exp);
					
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
					not_if1 = new Lincons1(Lincons1.SUP,exp2);
					//expression ex: 5>=x -> 5-x>=0
					into_if1 = new Lincons1(Lincons1.SUPEQ,exp1);
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
					not_if1 = new Lincons1(Lincons1.SUP,exp2);
					//expression ex: x>=5 -> x-5>=0
					into_if1 = new Lincons1(Lincons1.SUPEQ,exp1);
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
					not_if1 = new Lincons1(Lincons1.SUP,exp2);
					//expression ex: x>=q -> x-q>=0
					into_if1 = new Lincons1(Lincons1.SUPEQ,exp1);
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
					not_if1 = new Lincons1(Lincons1.SUPEQ,exp1);
					//expression ex: 5>x -> 5-x>0
					into_if1 = new Lincons1(Lincons1.SUP,exp2);
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
					not_if1 = new Lincons1(Lincons1.SUPEQ,exp2);
					//expression ex: x>5 -> x-5>0
					into_if1 = new Lincons1(Lincons1.SUP,exp1);
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
					not_if1 = new Lincons1(Lincons1.SUPEQ,exp2);
					//expression ex: x>q -> x-q>0
					into_if1 = new Lincons1(Lincons1.SUP,exp1);
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
					not_if1 = new Lincons1(Lincons1.SUP,exp2);
					//expression ex: 5<=x -> x-5>=0
					into_if1 = new Lincons1(Lincons1.SUPEQ,exp1);

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
					not_if1 = new Lincons1(Lincons1.SUP,exp2);
					//expression ex: x<=5 -> 5-x>=0
					into_if1 = new Lincons1(Lincons1.SUPEQ,exp1);

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
					not_if1 = new Lincons1(Lincons1.SUP,exp2);
					//expression ex: x<=q -> q-x>=0
					into_if1 = new Lincons1(Lincons1.SUPEQ,exp1);

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
					not_if1 = new Lincons1(Lincons1.SUPEQ,exp2);
					//expression ex: 5<x -> x-5>0
					into_if1 = new Lincons1(Lincons1.SUP,exp1);

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
					not_if1 = new Lincons1(Lincons1.SUPEQ,exp2);
					//expression ex: x<5 -> 5-x>0
					into_if1 = new Lincons1(Lincons1.SUP,exp1);

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
					not_if1 = new Lincons1(Lincons1.SUPEQ,exp2);
					//expression ex: x<q -> q-x>0
					into_if1 = new Lincons1(Lincons1.SUP,exp1);
					

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
					Linterm1 term2 = new Linterm1(var,new MpqScalar(-1));

					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{term},new MpqScalar(-1*(c.value)));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{term2},new MpqScalar(1*(c.value)));

					//expression ex: for 5==x -> x-5=0
					not_if1 = new Lincons1(Lincons1.EQ,exp);
					//expression ex: for 5!=x -> x-5<>0
					into_if1 = new Lincons1(Lincons1.SUP,exp);
					into_if2 = new Lincons1(Lincons1.SUP,exp2);

				} else {
					unhandled("eq expression with right of type: " + right.getType().toString());
				}
			} else if(left instanceof JimpleLocal){
				if(right instanceof IntConstant){
					sprint("eq expr with local int");
					String var = left.toString();

					IntConstant c = ((IntConstant) right);
					Linterm1 term = new Linterm1(var,new MpqScalar(1));
					Linterm1 term2 = new Linterm1(var,new MpqScalar(-1));
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{term},new MpqScalar(-1*(c.value)));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{term2},new MpqScalar(1*(c.value)));

					//expression ex: for x!=5 -> x-5=0
					not_if1 = new Lincons1(Lincons1.EQ,exp);
					//expression ex: for x!=5 -> x-5<>0
					into_if1 = new Lincons1(Lincons1.SUP,exp);
					into_if2 = new Lincons1(Lincons1.SUP,exp2);

				} else if(right instanceof JimpleLocal){
					sprint("eq expr with local local");
					String varl = left.toString();
					String varr = right.toString();

					Linterm1 terml = new Linterm1(varl,new MpqScalar(1));
					Linterm1 termr = new Linterm1(varr,new MpqScalar(-1));

					Linterm1 terml2 = new Linterm1(varl,new MpqScalar(-1));
					Linterm1 termr2 = new Linterm1(varr,new MpqScalar(1));
					
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{terml, termr},new MpqScalar(0));
					Linexpr1 exp2 = new Linexpr1(env,new Linterm1[]{terml2, termr2},new MpqScalar(0));

					//expression ex: for x==q -> q-x=0
					not_if1 = new Lincons1(Lincons1.EQ,exp);
					//expression ex: for x!=q -> x-q<>0
					into_if1 = new Lincons1(Lincons1.SUP,exp);
					into_if2 = new Lincons1(Lincons1.SUP,exp2);

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
		
		sprint("false: " + ow + " meet " + not_if1 +" join "+ not_if2);
		sprint("true:" + ow_branchout  + " meet "+ into_if1 +" join "+ into_if2);
		
		join(ow, not_if1, not_if2);
		join(ow_branchout, into_if1, into_if2);

		//AWrapper temp = ow;
		//ow = ow_branchout;
		//ow_branchout = temp;
		
		sprint("result false: " + ow);
		sprint("result true: "+ ow_branchout);
		
		ident--;
	}
	
	private void join(AWrapper wrapper, Lincons1 first, Lincons1 second) throws ApronException{
		if(second == null){
			wrapper.get().meet(man, first);
			return;
		}
		
		Abstract1 firstMeet = wrapper.get().meetCopy(man, first);
		Abstract1 secondMeet = wrapper.get().meetCopy(man, second);
		if(true == firstMeet.isBottom(man) && false == secondMeet.isBottom(man)){
			wrapper.set(secondMeet);
		}else if(false == firstMeet.isBottom(man) && true == secondMeet.isBottom(man)){
			wrapper.set(firstMeet);
		}else{
			wrapper.set(secondMeet); // set it to bottom! (both will be bottom here)
		}
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
				
				/* Example of handling assignment to a local variable */
				if (env.hasVar(name)){
					rAr = new Texpr1VarNode(name);
					xp = new Texpr1Intern(env, rAr);
					
					sprint("Assigning JimpleLocal with name " + name);
					o.assign(man, varName, xp, null);
				}else{
					sprint("env.hasVar("+name+") is false");
					String finalName = getConcreteInstanceVariableName(name);
					
					if(constructorCalls.containsKey(finalName)){
						sprint("constructorCalls contains '"+finalName+"'.");
						missileBatteryAssignments.put(varName, finalName);
						sprint("adding {"+varName+","+finalName+"} to missileBatteryAssignments");
					}
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
						sprint("will not assign " + varName + " JimpleLocal; env.hasVar("+name+") is false");
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
						sprint("assigning " + varName + " a JimpleLocal="+name);
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
			sprint("flowThrough called with " + s + ", in: " + current);

			Abstract1 in = current.get();
			Abstract1 out = new Abstract1(man, in);
			Abstract1 out_branchout = new Abstract1(man, env, true);
			AWrapper out_wrapper = new AWrapper(out);
			AWrapper out_branchout_wrapper = new AWrapper(out_branchout);	
			
			if (s instanceof DefinitionStmt) {
				// call handleDef
				Value left = ((DefinitionStmt) s).getLeftOp();
				Value right = ((DefinitionStmt) s).getRightOp();
				handleDef(out,left,right);
			} else if (s instanceof JIfStmt) {
				// check if this is a backjumpstmt(i.e. a loop), and if so, check it if has iterated at least 6 times.
				Tuple<Integer, List<Stmt>> loopDescriptor = backJumps.get((JIfStmt)s);
				if(loopDescriptor != null && loopDescriptor.item1 >= 6){
					fallOut.clear();
					//fallOut.add(newInitialFlow()); // add bottom
					out_branchout = in;
					fallOut.add(new AWrapper(new Abstract1(man, env,true)));
					sprint("Iterated more than 6 times => widening has occured. Moving away from loop...");
				
				}else{
					// call handleIf
					AbstractBinopExpr cond = (AbstractBinopExpr) ((JIfStmt) s).getCondition();
					sprint("condition: " + cond.toString());
					handleIf(cond,in, out_wrapper, out_branchout_wrapper);
					out = out_wrapper.get();
					out_branchout = out_branchout_wrapper.get();
					printGraph();
				}
			} else if (s instanceof JGotoStmt){
				JGotoStmt gotoStmt = (JGotoStmt)s;
				flowThrough(current, gotoStmt.getTarget(), fallOut, branchOuts);
			} else if (s instanceof InvokeStmt){
				// call handleInvoke
				InvokeStmt stmt = (InvokeStmt)s;
				handleMethodInvoke(in, stmt);
			} else if (s instanceof JReturnVoidStmt){
				// idk
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

		String missileBattery = getConcreteInstanceVariableName(base.getName());
		int sizeOfBattery = ((IntConstant)this.constructorCalls.get(missileBattery).get(0)).value;
		Interval sizeOfBatteryInterval = new Interval(0, sizeOfBattery - 1);
		
		Interval missileIdxInterval = getInterval(expr.getArg(0), o);
		sprint("missileIdxInterval = " + missileIdxInterval);
		sprint("Checking that " + missileIdxInterval + " is a subset of " + sizeOfBatteryInterval);
		if(sizeOfBatteryInterval.cmp(missileIdxInterval) != 1){
			sprint("** UNSAFE!! "+missileIdxInterval+" (missile index) is not subset of " + sizeOfBatteryInterval + " (size)");
			isSafe = false;
			return;
		}else{
			sprint("OK:)");
		}
		
		sprint("Checking that " + missileIdxInterval + " has not been already fired");
		List<Interval> prev = new ArrayList<Interval>();
		if(previousFires.containsKey(missileBattery)){
			prev = previousFires.get(missileBattery);
			int[] mBound = getEndpoints(missileIdxInterval);
			for(Interval p: prev){
				int[] pBound = getEndpoints(p);
				if(!(pBound[1]<mBound[0] || pBound[0] > mBound[1])){
					sprint("** UNSAFE!! "+missileIdxInterval+" (missile index) overlaps with already fired interval " + p);
					isSafe = false;
					break;
				}
			}
		} 
		prev.add(missileIdxInterval);
		previousFires.put(missileBattery, prev);
		
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
		try {
			//trg = new AWrapper(Abstract1.join(man, new Abstract1[]  {src1.get(), src2.get()}));
			trg.set(src2.get().joinCopy(man, src1.get()));
		} catch (ApronException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}		
		sprint("merge: " + src1+ " + " + src2 + " = " + trg);
		ident--;
	}
	
	

	/* It may be useful for widening */
	
	
	private Map<Stmt, Tuple<Integer, List<Stmt>>> backJumps = new HashMap<Stmt, Tuple<Integer, List<Stmt>>>();
	
	// Implement Join
	// src1 before iteration
	// src2 after executing loop block 
	@Override
	protected void merge(Unit u, AWrapper src1, AWrapper src2, AWrapper trg) {

		ident++;
		sprint("merge from unit " + u);
		if(false == u instanceof JIfStmt){
			//printGraph();
			merge(src1,src2,trg);
			return;
		}
		printGraph();
		JIfStmt u2 = (JIfStmt)u;
		Tuple<Integer, List<Stmt>> loopDescriptor = backJumps.get(u);
		try{
		if(loopDescriptor != null){ // this is a loop
			
			loopDescriptor.item1++;
			if(loopDescriptor.item1.intValue() >= 6){
				sprint("Iterated more than 5 times: " + loopDescriptor.item1);
				
				int countDefStatements = 0;
				for(Stmt s : loopDescriptor.item2){
					if(s instanceof DefinitionStmt)
						countDefStatements++;
				}
				
				Lincons1[] constraints = new Lincons1[countDefStatements];
				for(int i = 1; i < loopDescriptor.item2.size(); i++){
					Stmt target = loopDescriptor.item2.get(i);
					if(target instanceof DefinitionStmt){
						ident++;
						sprint("Widening " + target);
						Lincons1 result = widen((DefinitionStmt) target, src1, src2, trg);
						constraints[i-1] = (result);
						ident--;
					}
				}
				
				trg.set( src2.get().wideningThreshold(man, src1.get(), constraints) );
				
				sprint("Done with widening, result: " + trg);
			}else{
				merge(src1,src2,trg);
			}
			backJumps.put((Stmt)u, loopDescriptor);
		}
		
		}catch(ApronException ex){
			unhandled(ex.toString());
		}
		
		ident--;
		
	}
	
	private Lincons1 widen(DefinitionStmt defStmt, AWrapper src1, AWrapper src2, AWrapper trg) throws ApronException{
		if(defStmt.getRightOp() instanceof BinopExpr){
			BinopExpr binop = (BinopExpr)defStmt.getRightOp();
			
			JimpleLocal left = (JimpleLocal)binop.getOp1();
			Interval leftBound = src1.elem.getBound(man, left.getName());
			
			Interval widenedInterval = null;
			if(binop instanceof JAddExpr){
				AddExpr expr = (AddExpr)binop;
				IntConstant addTerm = (IntConstant) expr.getOp2();
				MpqScalar infty =  new MpqScalar();
				infty.setInfty(1);
				Interval currentBound = src1.elem.getBound(man, left.getName());
				
				if(addTerm.value < 0){
					Mpq q = new Mpq();
					int round = 2;
					currentBound.sup.toMpq(q, round); // upper bound of the assignment target
					Linterm1 term = new Linterm1(left.getName(),new MpqScalar(-1));
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{term}, new MpqScalar(q));
					//expression ex: oo -x > 0
					//c = new Lincons1(Lincons1.SUP, exp);
					Lincons1 c = new Lincons1(Lincons1.SUPEQ, exp);
					Lincons1[] arr = new Lincons1[1];
					arr[0] = c;
					Abstract1 widened = src2.elem.wideningThreshold(man, src1.elem, arr);
					Interval b = widened.getBound(man, left.getName());
					sprint("Widened Interval for target: " + b + " (was " + currentBound + ")");

					return c;					
				}else if(addTerm.value > 0){
					Mpq q = new Mpq();
					int round = 2;
					currentBound.inf.toMpq(q, round); // upper bound of the assignment target
					q.neg();
					Linterm1 term = new Linterm1(left.getName(),new MpqScalar(1));
					Linexpr1 exp = new Linexpr1(env,new Linterm1[]{term}, new MpqScalar(q));
					
					//expression ex: x = 10, x-10 >= 0 ---> x = [10, +oo]
					
					Lincons1 c = new Lincons1(Lincons1.SUPEQ, exp);
					Lincons1[] arr = new Lincons1[1];
					arr[0] = c;
					Abstract1 widened = src2.elem.wideningThreshold(man, src1.elem, arr);
					Interval b = widened.getBound(man, left.getName());
					sprint("Widened Interval for target: " + b + " (was " + currentBound + ")");

					return c;
				}else{
					// i guess if this is when you add 0
					sprint("Sign is null???");
				}
			}else{
				unhandled("(merge) binary operator other than JAddExpr (was " + binop.getOp2().getClass() + ")");
			}
		}
		return null;
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


	public static Manager man;
	private Environment env;
	public UnitGraph g;
	public String local_ints[]; // integer local variables of the method
	public static String reals[] = { "foo" };
	public SootClass jclass;
	private int ident = 0;
	private HashMap<String, List<Value>> constructorCalls;
	private HashMap<String, String> missileBatteryAssignments;
	private HashMap<String, List<Interval>> previousFires;
	
	public boolean isSafe = true;
	
	private String getConcreteInstanceVariableName(String variableName){
		String finalName = variableName;
		while(missileBatteryAssignments.containsKey(finalName)){
			finalName = missileBatteryAssignments.get(finalName);
		}
		
		return finalName;
	}
	
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
	
	private int[] getEndpoints(Interval i){
		String s = i.toString();
		String lower = s.substring(1, s.lastIndexOf(","));
		String upper = s.substring(s.lastIndexOf(",")+1,s.lastIndexOf("]"));
		int l = Integer.parseInt(lower);
		int u = Integer.parseInt(upper);
		int[] bound = new int[]{l,u};
		return bound;
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
		//System.out.println(g.getBody().toString());
	}
}
