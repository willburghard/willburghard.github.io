import java.io.*;
import java.util.Scanner;
import static java.lang.Math.*;
import java.util.LinkedList;
import java.util.Stack;
import java.util.ArrayList;
import java.util.Iterator;

/** 
    Represent a CNF problem to solve.  
    This version allows setting and
    unsetting of clauses and variables to implement backtracking.

    @author Will Burghard
*/
public class Formula {

    // For easy debug printing.  DO NOT call from final solution
    // as it will slow things down greatly.
    //public static void p(boolean b,String x) {if (b) System.out.println(x);}	

    private String name; // problem name
    private int nvar; // number of vars
    private int nclauses; // number of clauses
    private int form[ ][ ]; // formula broken up by clauses

    private int vars[ ]; // variable assignment (true,false,NOTASSIGNED)

    public static final int MAXCLAUSELEN = 3; // limits us to 3SAT
    public static final int NOTASSIGNED = 0; // unassigned variable
    public static final int TRUE = 2;
    public static final int FALSE = 1;
    final char COMMENT = 'c';
    final String PROBLEM =  "p";
    final String CNF =  "cnf";
    // stack of clauses for backtracking
    private Stack<LinkedList<Integer>> clauseStack; 
    private Iterator<Integer> iter;  // re-usable iterator
    private int[][] clauses; //2d array used to store variable states at different points. 0 is unassigned, 1 is false(deleted) integer, 2 is true(indicating clause is deleted).
	private int[] a; //Array representing empty clause to compare to clauses
	

    /** 
	Assumes file name of DIMAC format 3SAT problem. 
	Loads file into object.  Do not modify this method!
	@param fname file name to open
    */
    public Formula(String fname) {
	Scanner s = null;
	try {
	    this.name = fname;
	    s = new Scanner(new BufferedReader(new FileReader(fname)));
	    String line = null;
	    // Remove comments
	    while (s.hasNextLine()) {
		line = s.nextLine();
		if (line.charAt(0) != COMMENT)  break;
	    }
	    // Extract problem
	    String[ ] token = line.split("\\s+");
	    //System.out.println("problem: " + line);
	    if ( token.length < 4 || !token[0].equals(PROBLEM) || !token[1].equals(CNF)) {
		System.err.println("Error in input; bad problem line found");
		System.err.println(line);
		return;
	    }
	    this.nvar = Integer.parseInt(token[2]);
	    this.nclauses = Integer.parseInt(token[3]);
	    this.form = new int[nclauses][ ];
	    this.clauses = new int[nclauses][];
	    // load integers representing clause using standard DIMACS format
	    // assume  0 at end of each clause
	    int clausenum = 0;
	    int [ ] tmp = new int[MAXCLAUSELEN+1]; // temporary space
	    int i = 0;
	    while (s.hasNextInt()) {
		i = 0; // load one clause
		while (s.hasNextInt() && i < tmp.length) {
		    tmp[i] =  s.nextInt();
		    if (tmp[i] == 0)  break; // end of clause
		    i++;
		}
		this.form[clausenum] = new int[i]; // copy clause to formula
		this.clauses[clausenum] = new int[i]; //Fill "clauses" with zeros
		for (int k = 0; k < i; k++) {  
			this.form[clausenum][k] = tmp[k];
			this.clauses[clausenum][k] = 0;
		}
		clausenum++;
	    }
	
	    vars = new int[nvar];
	    
	} catch (FileNotFoundException ex) {
	    ex.printStackTrace();
	    return;
	} finally {
	    if (s != null) s.close();
	}
	initBacktrack();
    }

    /**
       Print var assignment.
    */
    void printAssignment() {
	for (int i = 0; i < nvar; i++) System.out.print(vars[i] + " ");
	System.out.println();
    }

    /** Initialize vars for backtracking:

	vars: t/f/notassigned array for current assignment

	clauseStack: stack of active clauses we backtrack to when
	assignment fails.
    */
    private void initBacktrack() {
    	for(int g = 0; g < form.length; g++) {
    		for(int h = 0; h < form[g].length; h++) {
    			System.out.print(form[g][h]);
    		}
    		System.out.println();
    	}
    	clauseStack = new Stack<LinkedList<Integer>>();
    	for(int w = 0; w < vars.length; w++) {
    		vars[w] = NOTASSIGNED;
    	}
    	LinkedList<Integer> initClauses = new LinkedList<Integer>();
    	for(int e = 0; e < form.length; e++) {
    		Integer g = e;
    		initClauses.add(g);    	
    		}
    	this.clauseStack.push(initClauses);
       
    }


    /**
       @return formula as string
    */
    public String toString() {
	StringBuilder sb = new StringBuilder();

	for (int i = 0; i < form.length; i++) {
	    for (int j = 0; j < form[i].length; j++) {
		sb.append(form[i][j]);
		sb.append("\t");
	    }
	    sb.append("\n");
	}
	return sb.toString();
    }

	
    /**
       @return branch variable
       Returns -1 if no variable to try exists.
    */
    int selectBranchVar ( ) {
	for (int i = 0; i < nvar; i++) 
	    if (vars[i] == NOTASSIGNED) return ++i;
	return -1;
    }

    /**
       @return true if the formula has an empty clause, false otherwise
    */
    boolean hasEmptyClause () {
       for(int o = 0; o < clauses.length; o++) {
    	   if (isEmptyClause(o)) {
    		   return true;
    	   }
       }
       return false;
    }
	
    /**
       @return true if the formula has no clauses left, false otherwise
    */
    boolean isEmpty ( ) {
    	return clauseStack.peek().isEmpty();
    }

    /**
       @return true if the clause at index c is empty
    */
    boolean isEmptyClause ( int c ) {
    	for(int s = 0; s < clauses[c].length; s++){
    		if(clauses[c][s] != 1) { //If all variables in the corresponding row in "clauses" are 1, then all variables are false/deleted, so clause is empty
    			return false;
    		}
    		
    	}
    	return true;
    }
    /**
       @return true iff formula[clz] contains var.
    */
    private boolean inClause(int clz,int var) {
    	for(int q = 0; q < form[clz].length; q++) {
    		if (form[clz][q] == var) {
    			return true;
    		}
    	}
	return false;
    }

    /**
     Set given variable to given true/false value.
     Variable value is positive, but in formula is posivite or negative.
     Will remove clauses containing true var value from consideration.
     Will remove variables false var value from clauses.
     @param var index of var to set.
     @param val t/f value to set var.
    */
    
    void setVar (int var, boolean val) {
    	if(val) {
    		vars[var-1] = TRUE;
    	}
    	else {
    		vars[var-1] = FALSE;
    	}
    	LinkedList<Integer> stackTop = new LinkedList<Integer>(); //New stack frame 
    	for(int k = 0; k < clauseStack.peek().size(); k++) {
    		stackTop.add(clauseStack.peek().get(k)); //New stack frame should be equivalent to last
    	}
    	clauseStack.push(stackTop);
    		for(int h = 0; h < stackTop.size(); h++) { //Only look through hereto unsatisfied clauses
    			Integer x = stackTop.get(h);
    		    for(int y = 0; y < form[x].length; y++)
    		    	if(form[x][y] == var) { //var is in clause
    		    		if(val) {
    		    			clauses[x][y] = 2; //2 indicates true, so clause is deleted
    		    			Integer n = x;
    		    			boolean f = clauseStack.peek().remove(n); //delete clause
    		    		    h--;
    		    		}
    		    		else {
    		    			clauses[x][y] = 1; //1 indicates false, so variable should be deleted
    		    		}
    		    	}
    		    	else if(form[x][y] == (0-var)) { //-var is in clause
    		    		if(val) {
    		    			clauses[x][y] = 1; //-true means false, so var is deleted
    		    		}
    		    		else {
    		    			clauses[x][y] = 2;
    		    			Integer n = x;
    		    			boolean f = clauseStack.peek().remove(n);
    		    			h--;
    		    		}
    		    	}
    		}
    		
    	
    }
	
    /**
       @param variable to unset (only positive values allowed)
       Set given variable to NOTASSIGNED.
       Flagged instances in clauses must be unflagged.
       Must backtrack to set of clauses at point when var was assigned.
    */
    void unset (int var) {
    	vars[var-1] = NOTASSIGNED;
    	clauseStack.pop(); //Pop off stack frame to backtrack
    	for(int b = 0; b < form.length; b++) { 
    		for(int c = 0; c < form[b].length; c++) {
    			if(form[b][c] == var) {
    				clauses[b][c] = 0; //Set variable in "clauses" to 0 (unassigned)
    			}
    			else if(form[b][c] == (0-var)) {
    				clauses[b][c] = 0;
    			}
    		}
    	}
    }
    
   

}
