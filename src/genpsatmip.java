//     GenPSAT SOLVER AM & FC & CC
// 	   decides the satisfiability of linear inequalities involving probabilities of classical propositional formulas
//     Copyright (C) 2016  Carlos Caleiro, Filipe Casal, Andreia Mordido

//     This program is free software: you can redistribute it and/or modify
//     it under the terms of the GNU General Public License as published by
//     the Free Software Foundation, either version 3 of the License, or
//     (at your option) any later version.

//     This program is distributed in the hope that it will be useful,
//     but WITHOUT ANY WARRANTY; without even the implied warranty of
//     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//     GNU General Public License for more details.

//     You should have received a copy of the GNU General Public License
//     along with this program.  If not, see <http://www.gnu.org/licenses/>.

import gurobi.*;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileInputStream;

import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

class probterm {
        double coef;
        int formula;

   // constructor
   public probterm(double c, int m ) {
      this.coef = c;
      this.formula = m;
   }
 }

 class instance {
        int npropvars;
        int nclauses;
        int nprobabilities;
        int[][] phi;
        ArrayList<List<probterm>> probform;
        String[] bowtie;
        Double[] indepterm;

    // constructor
    public instance(int n, int m, int q , int[][] phi, ArrayList<List<probterm>> probform,
      String[] bowtie,  Double[] indepterm) {
       this.npropvars = n;
       this.nclauses = m;
       this.nprobabilities = q;
       this.phi = phi;
       this.probform = probform;
       this.bowtie = bowtie;
       this.indepterm = indepterm;
    }
}

public class genpsatmip {

	private static List<String> variables;
	private static List<String> formulasToCheck;
	public static List<String> propositionalFormulas;
	private static List<String> subPropositionalFormulas;
	public static Map<Integer, List<Double>> multiplicaoSubPropositionalFormulas;
	public static List<Double> finalValuesPropositionalFormulas;
	public static int numFormulasToCheck;
	public static int numSubPropositionalFormulas;
	public static int numVariables;


public static instance parser(String fileName){
	try
    {
    	Scanner in = new Scanner(new FileInputStream(fileName));

        //ignore comment header
        String problemLine = in.nextLine();
        while (problemLine.startsWith("c"))
        {
            problemLine = in.nextLine();
    	}

		//process the problem line
		String[] params = problemLine.split(" ");
		if (!params[0].equals("p"))
		{
			System.err.println("ERROR: file appears to miss the problem line!");
			return null;
		}
		if (!params[1].equals("cnf"))
		{
			System.err.println("ERROR: Parsing a non-CNF Dimacs file");
		}

		int n, m, q;

		if(params.length == 5){
			//variable n (number of prop variables)
			n = Integer.parseInt(params[2]);
			// variable m (number of prop clauses)
			m = Integer.parseInt(params[3]);
			//variable q (number of probabilist formulas)
			q = Integer.parseInt(params[4]);
		}
		else{
			System.err.println("p line is supposed to contain");
			System.err.println("p cnf #propvariabls #clauses #probabform");
			return null;
		}

		int i=0;
		int lineID = 0;
		String currentLine;
		String[] tokens;
		List<Integer> currentClause = new LinkedList<Integer>();
		int[][] phi = new int[m][3]; //3CNF
		//parse propositional clauses
		while (lineID < m)
		{
			currentLine = in.nextLine();
			tokens = currentLine.split("\\s");
			if (tokens[0].equals("c"))
			{
			    //ignore other comments
			}
			else
			{
				if(tokens.length != 4)
					System.err.println("please insert clauses in 3CNF");
				for (i = 0; i < tokens.length; i++)
				{
		  			Integer literal = Integer.parseInt(tokens[i]);
					if (literal == 0)
					{
		    			break;
		  			}
		  			else
		  			{
		    			// phi represents proprositional formula in CNF with m clauses
		    			phi[lineID][i] = literal;
		  			}
				}
			}
			lineID++;
		}


		// parse probabilistic formulas
		i=0;
		lineID = 0;
		String[] part, tuple;
		Double coeftemp;
		Integer formtemp;
		String term;
		Double alpha;
		Double[] indepterm = new Double[q];
		String[] bowtie = new String[q];
		ArrayList<List<probterm>> arrayofprobformulas = new ArrayList<List<probterm>>();
		for(int j=0; j<q; j++)
		{
			arrayofprobformulas.add(new LinkedList<probterm>());
		}
		while (lineID<q)
		{
			currentLine = in.nextLine();
			tokens = currentLine.split("\\s");
			switch(tokens[0])
			{
				case "c":
					break;
				case "GE": case "SG": case "LE": case "SL":  case "EQ": case "DI":
					//treat formulas a1P(A1) + ... + anP(an) |><| q
					for(int k = 1; k < tokens.length-1; k++)
					{
						term = tokens[k];
						part = term.split("\\(");
						for(String pair : part)
						{
							if(!pair.trim().equals(""))
							{
								tuple = pair.split("\\)");
								coeftemp = Double.parseDouble(tuple[0]);
								formtemp = Integer.parseInt(tuple[1]);
								probterm p = new probterm(coeftemp, formtemp);
								arrayofprobformulas.get(lineID).add(p );
							}
						}
					}
					indepterm[lineID] = Double.parseDouble(tokens[tokens.length-1]);
					bowtie[lineID] = tokens[0];
					break;
				default:
					throw new IllegalArgumentException("Invalid inequality used " + tokens[0] + " "+ currentLine);
			}
			lineID++;
        }

        instance inst = new instance(n, m, q, phi, arrayofprobformulas, bowtie, indepterm );
        return inst;
    }

    catch (FileNotFoundException e)
    {
		System.err.println("ERROR: Dimacs CNF file not found: " + fileName);
		System.err.println("       Returning empty SAT instance!");
		return null;
	}
}



public static void main(String[] args){
    try 
    {	
    	String fileinst = "";
    	if (args.length == 1 ){
    		fileinst = args[0];
        }
        else{
        	System.out.println("usage: java genpsatmip filename");
        	return ;
        }

    	GRBEnv    env   = new GRBEnv("mip.log");
        GRBModel  model = new GRBModel(env);

        variables = new ArrayList<String>();
        formulasToCheck = new ArrayList<String>();
        propositionalFormulas = new ArrayList<String>();
        subPropositionalFormulas = new ArrayList<String>();
        multiplicaoSubPropositionalFormulas = new HashMap<Integer, List<Double>>();
        finalValuesPropositionalFormulas = new ArrayList<Double>();
        numFormulasToCheck = 0;

        instance inst = parser(fileinst);

        // INPUT VARIABLES
        int n = inst.npropvars;
        int m = inst.nclauses;
        int q = inst.nprobabilities;
        int[][] phi = inst.phi;
        ArrayList<List<probterm>> probform = inst.probform;
        String[] bowtie = inst.bowtie;
        Double[] indepterm = inst.indepterm;


    	int existskappa = 0;
    	int existsstrict = 0;


    	// LP variables
		GRBVar[][] a = new GRBVar[n][n+1];
		for(int i=0; i<n; i++) {
			for(int j=0; j<n+1; j++) {
				a[i][j] = model.addVar(0.0, 1.0, 0.0, GRB.BINARY, "a"+i+j);
			}
		}

		GRBVar[][] b = new GRBVar[n][n+1];
		for(int i=0; i<n; i++) {
			for(int j=0; j<n+1; j++) {
				b[i][j] = model.addVar(0.0, 1.0, 0.0, GRB.CONTINUOUS, "b"+i+i+j);
			}
		}

		// vector p is the probability distribution over the valuations
		GRBVar[] p = new GRBVar[n+1];
		for (int i=0; i<n+1 ; i++ ) {
			p[i] = model.addVar(0.0, 1.0, 0.0, GRB.CONTINUOUS, "p"+i);
		}

		GRBVar epsilon = model.addVar(0.0, GRB.INFINITY, 0.0, GRB.CONTINUOUS, "epsilon");

		GRBVar[] kappa = new GRBVar[n];
		for (int i=0; i<n ; i++ ) {
			kappa[i] = model.addVar(0.0, 1.0, 0.0, GRB.CONTINUOUS, "kappa"+i);
		}

		GRBVar[] diffaux = new GRBVar[q];

		model.getEnv().set("OutputFlag", "0");

		model.update();

		GRBLinExpr constraint = new GRBLinExpr();
		GRBLinExpr constraint2 = new GRBLinExpr();
		GRBLinExpr diffbound = new GRBLinExpr();

		for (int i=0; i<q ; i++ ) 
		{
			constraint = new GRBLinExpr();
			constraint2 = new GRBLinExpr();
			diffbound = new GRBLinExpr();
			for (int j=0; j<probform.get(i).size() ; j++ ) {
				constraint.addTerm(probform.get(i).get(j).coef, kappa[probform.get(i).get(j).formula-1]);
				constraint2.addTerm(probform.get(i).get(j).coef, kappa[probform.get(i).get(j).formula-1]);
			}
			switch(bowtie[i])
			{
				case "EQ":
					model.addConstr(constraint, GRB.EQUAL, indepterm[i], "probconstr"+i);
					break;
				case "GE":
					model.addConstr(constraint, GRB.GREATER_EQUAL, indepterm[i], "probconstr"+i);
					break;
				case "LE":
					model.addConstr(constraint, GRB.LESS_EQUAL, indepterm[i], "probconstr"+i);
					break;
				case "SL":
					constraint.addTerm(1.0, epsilon);
					model.addConstr(constraint, GRB.LESS_EQUAL, indepterm[i], "probconstr"+i);
					existsstrict =1;
					break;
				case "SG":
					constraint.addTerm(-1.0, epsilon);
					model.addConstr(constraint, GRB.GREATER_EQUAL, indepterm[i], "probconstr"+i);
					existsstrict =1;
					break;
				case "DI":
					double magnitude = Math.abs(indepterm[i])+1;
					for(int l=0; l<probform.get(i).size(); l++){
						magnitude += Math.abs(probform.get(i).get(l).coef);
					}

					diffaux[i] = model.addVar(0.0, 1.0, 0.0, GRB.BINARY, "diffaux" +i);
					model.update();

					constraint.addConstant(-indepterm[i]);
					constraint2.addConstant(-indepterm[i]);

					diffbound.addTerm(magnitude, diffaux[i]);
					constraint.addTerm(1.0, epsilon);

					model.addConstr(constraint, GRB.LESS_EQUAL, diffbound, "probconstr1"+i);
					constraint2.addTerm(-1.0, epsilon);
					diffbound.addConstant(-magnitude);

					model.addConstr(constraint2, GRB.GREATER_EQUAL, diffbound, "probconstr2"+i);
					existsstrict =1;
					break;
          		default:
					throw new IllegalArgumentException("Invalid inequality used " + bowtie[i] );
			}
		}

		//Create constraints
		GRBLinExpr expr = new GRBLinExpr();
		for (int j=0; j< n+1 ; j++ ) 
		{
			for(int i=0; i<m; i++) 
			{
				expr = new GRBLinExpr();
				for(int k=0; k<3; k++) { //clause has 3 literals
					if(phi[i][k]<0){
						expr.addConstant(1.0);
						expr.addTerm(-1.0, a[-phi[i][k]-1][j]);
					}
					else if (phi[i][k]>0) {
						expr.addTerm(1.0, a[phi[i][k]-1][j]);
					}
					else if (phi[i][k]==0) {
						expr.addConstant(0.0);
						System.out.println("Something happened with phi.");
					}
				}
				model.addConstr(expr, GRB.GREATER_EQUAL, 1.0, "a"+j+i);
			}
		}

		GRBLinExpr expr1 = new GRBLinExpr();
		GRBLinExpr expr2 = new GRBLinExpr();
		for(int i=0; i<n; i++)
		{
			expr = new GRBLinExpr();
			for(int j=0; j<n+1; j++)
			{
				expr.addTerm(1.0, b[i][j]);
				expr1 = new GRBLinExpr();
				expr1.addTerm(1.0, b[i][j]);
				model.addConstr(expr1, GRB.GREATER_EQUAL, 0.0, "b-1"+j+i);
				model.addConstr(expr1, GRB.LESS_EQUAL, a[i][j], "b-2"+j+i);
				expr2 = new GRBLinExpr();
				expr2.addTerm(1.0, a[i][j]);
				expr2.addTerm(1.0, p[j]);
				expr2.addConstant(-1.0);
				model.addConstr(expr1, GRB.GREATER_EQUAL, expr2, "b-3"+j+i);
				model.addConstr(expr1, GRB.LESS_EQUAL, p[j], "b-4"+j+i);
			}
			model.addConstr(expr, GRB.EQUAL, kappa[i], "kappa"+i);
		}

		expr = new GRBLinExpr();
		for (int j=0; j<n+1; j++) {
			expr.addTerm(1.0, p[j]);
		}
		model.addConstr(expr, GRB.EQUAL, 1.0, "prob");

		expr.addTerm(1.0, epsilon);
		model.addConstr(expr, GRB.EQUAL, 1.0, "sumsone");


		model.update();

		expr1 = new GRBLinExpr();
		if(existsstrict ==1){
			expr1.addTerm(1.0, epsilon);
			model.setObjective(expr1, GRB.MAXIMIZE);
		}
		model.update();
		model.write("out.lp");

		model.optimize();

		int optimstatus = model.get(GRB.IntAttr.Status);
		double objval = 0;
		if (optimstatus == GRB.Status.OPTIMAL) {
			objval = model.get(GRB.DoubleAttr.ObjVal);
			if(objval <= 0 && existsstrict==1 ){
				System.out.println("UNSAT");
			} else{
				System.out.println("SAT");
			}
		}
		else if (optimstatus == GRB.Status.INF_OR_UNBD) {
			System.out.println("INF_OR_UNBD");
		return;
		} else if (optimstatus == GRB.Status.INFEASIBLE) {
			System.out.println("INFEASIBLE");
			return;
		} else if (optimstatus == GRB.Status.UNBOUNDED) {
			System.out.println("UNBOUNDED");
			return;
		} else {
			System.out.println("Optimization was stopped with status = " + optimstatus);
			return;
		}

	      // Dispose of model and environment
		model.dispose();
		env.dispose();

		} catch (GRBException e) {
			System.out.println("Error code: " + e.getErrorCode() + ". " +
	                         e.getMessage());
	    }
	}
}
