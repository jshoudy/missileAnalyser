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
import soot.jimple.IntConstant;
import soot.jimple.Stmt;
import soot.jimple.internal.AbstractBinopExpr;
import soot.jimple.internal.JAddExpr;
import soot.jimple.internal.JDivExpr;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JGeExpr;
import soot.jimple.internal.JGtExpr;
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
		System.out.println("successfully constructed");

	}

	void run() {
		System.out.println("called run");
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

		Value left = expr.getOp1();
		Value right = expr.getOp2();

		System.out.println("called handleIf with expr: " + expr.toString());
		
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
	}

	// handle assignments
	private void handleDef(Abstract1 o, Value left, Value right)
			throws ApronException {
		
		System.out.println("handleDef called with: ");
		System.out.println("    left = " + left.getType());
		System.out.println("    right = " + right.getType());
		Texpr1Node lAr = null;
		Texpr1Node rAr = null;
		Texpr1Intern xp = null;

		if (left instanceof JimpleLocal) {
			String varName = ((JimpleLocal) left).getName();

			if (right instanceof IntConstant) {
				/* Example of handling assignment to an integer constant */
				IntConstant c = ((IntConstant) right);

				rAr = new Texpr1CstNode(new MpqScalar(c.value));
				xp = new Texpr1Intern(env, rAr);

				o.assign(man, varName, xp, null);

			} else if (right instanceof JimpleLocal) {
				/* Example of handling assignment to a local variable */
				if (env.hasVar(((JimpleLocal) right).getName())) {
					rAr = new Texpr1VarNode(((JimpleLocal) right).getName());
					xp = new Texpr1Intern(env, rAr);
					o.assign(man, varName, xp, null);
				}
			} else if (right instanceof BinopExpr) {
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
			} else {
				System.out.println(right.toString());
				unhandled("expr of type 3 " + right.getType());
			}
		}
	}

	@Override
	protected void flowThrough(AWrapper current, Unit op,
			List<AWrapper> fallOut, List<AWrapper> branchOuts) {

		Stmt s = (Stmt) op;
		Abstract1 in = ((AWrapper) current).get();

		Abstract1 o;
		
		System.out.println("flowThrough called with: ");
		System.out.println("    current: " + s.toString());
		System.out.println("    op: " + op.toString());

		try {
			o = new Abstract1(man, in);
			Abstract1 o_branchout = new Abstract1(man, in);

			if (s instanceof DefinitionStmt) {
				// call handleDef
				Value left = ((DefinitionStmt) s).getLeftOp();
				Value right = ((DefinitionStmt) s).getRightOp();
				System.out.println("    def st left: " + left.getType() + " " + left.toString());
				System.out.println("    def st right: " + right.getType() + " " + right.toString());
				handleDef(o,left,right);
				
			} else if (s instanceof JIfStmt) {
				// call handleIf
				AbstractBinopExpr cond = (AbstractBinopExpr) ((JIfStmt) s).getCondition();
				System.out.println("    condition: " + cond.toString());
				handleIf(cond,in,new AWrapper(o),new AWrapper(o_branchout));
			}
		} catch (ApronException e) {
			// TODO Auto-generated catch block
			System.out.println("reached catch block in flowThrough");
			e.printStackTrace();
		}
	}

	// Initialize starting label (top)
	@Override
	protected AWrapper entryInitialFlow() {
		System.out.println("called entryIntitialFlow");
		Abstract1 top = null;
		try {
			top = new Abstract1(man,env);
			System.out.println(top.toString());
		} catch (ApronException e) {
			// TODO Auto-generated catch block
			System.out.println("reached catch blcok of entryInitialFlow");
			e.printStackTrace();
		}
		return new AWrapper(top);	
	}

	// Implement Join
	@Override
	protected void merge(AWrapper src1, AWrapper src2, AWrapper trg) {
		System.out.println("merge called with src1: " + src1.toString());
		System.out.println("                  src2: " + src2.toString());
		System.out.println("                  trg: " + trg.toString());
	}

	// Initialize all labels (bottom)
	@Override
	protected AWrapper newInitialFlow() {
		System.out.println("called newInitialFlow");
		Abstract1 bot = null;
		try {
			bot = new Abstract1(man,env,true);
			System.out.println(bot.toString());
		} catch (ApronException e) {
			// TODO Auto-generated catch block
			System.out.println("reached catch block in newInitialFlow");
			e.printStackTrace();
		}
		return new AWrapper(bot);	
	}

	@Override
	protected void copy(AWrapper source, AWrapper dest) {
		System.out.println("called copy");
		dest.copy(source);
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

}
