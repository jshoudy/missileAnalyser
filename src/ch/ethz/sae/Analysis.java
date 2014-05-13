package ch.ethz.sae;

import java.util.Iterator;
import java.util.List;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Manager;
import apron.MpqScalar;
import apron.Polka;
import apron.Texpr1CstNode;
import apron.Texpr1Intern;
import apron.Texpr1Node;
import apron.Texpr1VarNode;
import soot.IntegerType;
import soot.Local;
import soot.SootClass;
import soot.Unit;
import soot.Value;
import soot.jimple.BinopExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.Expr;
import soot.jimple.IdentityStmt;
import soot.jimple.IntConstant;
import soot.jimple.NewExpr;
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

		buildEnvironment();
		instantiateDomain();
		sprint("successfully constructed");

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
		
		// handle JEqExpr, JNeExpr and the rest...
		if(expr instanceof JEqExpr){
			JEqExpr j = new JEqExpr(left,right);
			
		} else if(expr instanceof JGeExpr){
			JGeExpr j = new JGeExpr(left,right);
			
		} else if(expr instanceof JGtExpr){
			JGtExpr j = new JGtExpr(left,right);
			
		} else if(expr instanceof JLeExpr){
			JLeExpr j = new JLeExpr(left,right);
			
		} else if(expr instanceof JLtExpr){
			JLtExpr j = new JLtExpr(left,right);
			
		} else if(expr instanceof JNeExpr){
			JNeExpr j = new JNeExpr(left,right);
			
		} else {
			unhandled("expr of type 1 " + expr.getType());
		}
		ident--;
	}

	// handle assignments
	private void handleDef(Abstract1 o, Value left, Value right)
			throws ApronException {
		ident++;
		
		sprint("handleDef called with " + 
				right.getClass().toString().substring(right.getClass().toString().lastIndexOf(".")+1) + ": "
				+ left + " = " + right);
		
		Texpr1Node lAr = null;
		Texpr1Node rAr = null;
		Texpr1Intern xp = null;

		if (left instanceof JimpleLocal) {
			ident++;
			String varName = ((JimpleLocal) left).getName();
			sprint("varName = " + varName);
			if (right instanceof IntConstant) {
				sprint("Entering IntConstant");
				/* Example of handling assignment to an integer constant */
				IntConstant c = ((IntConstant) right);

				rAr = new Texpr1CstNode(new MpqScalar(c.value));
				xp = new Texpr1Intern(env, rAr);

				sprint("    Assigning IntConstant of value " + c.value);
				o.assign(man, varName, xp, null);
			} else if (right instanceof JimpleLocal) {
				sprint("Entering JimpleLocal");
				/* Example of handling assignment to a local variable */
				if (env.hasVar(((JimpleLocal) right).getName())) {
					rAr = new Texpr1VarNode(((JimpleLocal) right).getName());
					xp = new Texpr1Intern(env, rAr);
					
					sprint("Assigning JimpleLocal with name " + ((JimpleLocal) right).getName());
					o.assign(man, varName, xp, null);
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
				
				if(right instanceof JMulExpr){
					JMulExpr j = new JMulExpr(l,r);
				} else if(right instanceof JSubExpr){
					JSubExpr j = new JSubExpr(l,r);
					
				} else if(right instanceof JAddExpr){
					JAddExpr j = new JAddExpr(l,r);
					
				} else if(right instanceof JDivExpr){
					JDivExpr j = new JDivExpr(l,r);
					
				} else {
					unhandled("expr of type 2 " + right.getType());
				}
				
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
		Abstract1 in = ((AWrapper) current).get();

		Abstract1 o;
		
		sprint("flowThrough called with " + last(s.getClass().toString()));
		//sprint("    in: " + in.toString());
		//sprint("    op: " + op.toString());

		try {
			o = new Abstract1(man, in);
			Abstract1 o_branchout = new Abstract1(man, in);

			if (s instanceof DefinitionStmt) {
				// call handleDef
				Value left = ((DefinitionStmt) s).getLeftOp();
				Value right = ((DefinitionStmt) s).getRightOp();
				sprint("DefinitionStmt left: " + left.getType() + " " + left.toString());
				sprint("DefinitionStmt right: " + right.getType() + " " + right.toString());
				handleDef(o,left,right);
				
			} else if (s instanceof JIfStmt) {
				// call handleIf
				AbstractBinopExpr cond = (AbstractBinopExpr) ((JIfStmt) s).getCondition();
				sprint("condition: " + cond.toString());
				handleIf(cond,in,new AWrapper(o),new AWrapper(o_branchout));
			} else  {
				sprint("Unhandled operation: " + last(s.getClass().toString()));
			}
		} catch (ApronException e) {
			// TODO Auto-generated catch block
			sprint("reached catch block in flowThrough");
			e.printStackTrace();
		}
		ident--;
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
			sprint("reached catch blcok of entryInitialFlow");
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
	
	public String last(String s){
		return s.substring(s.lastIndexOf(".")+1);
	}
	
	public void sprint(String what){
		for (int i = 0; i < this.ident; i++){
			System.out.print("  ");
		}
		System.out.println(what);
	}

}
