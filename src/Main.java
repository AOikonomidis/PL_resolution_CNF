/*

 	@authors: Andrew Oikonomidis & Andronikos Koutroumpelis

 */

import java.io.*;
import java.util.*;

public class Main {

	private static File file = null;
	private static BufferedReader reader = null;
	private static String line;
	private static final String fileName = "./../KB.txt";

	public static Vector<String> splitKB = new Vector<String>();
	public static int counter = 0;
	public static Scanner input = new Scanner(System.in);
	public static Scanner yesNo = new Scanner(System.in);

	public static void main(String args[]) {
		
		readKB();
		mainApp(userInput());

	}

	// loading our KB from file
	public static void readKB() {
		
		try {
			file = new File(fileName);
		} catch (NullPointerException e) {
			System.out.println("ERROR! File not found!");
		}

		try {
			reader = new BufferedReader(new FileReader(file));
		} catch (FileNotFoundException e) {
			System.out.println("Error opening the file!");
		}

		try {
			line = reader.readLine();
		} catch (IOException e) {
			System.out.println("Error loading file!");
		}

		try {
			reader.close();
		} catch (IOException e) {
			System.out.println("Error closing file!");
		}

		System.out.println("\nKB is: " + line + "\n");

		String[] split = line.split("\\*"); // first split of our KB string, removing all the *
		String[] str;
		counter += split.length; // how many subclauses we have

		for (int i=0; i<split.length; i++) {
			str = split[i].split("\\,"); // second split of our KB string, removing all the ,
			str[0] = str[0].replace("(", ""); // removing left parenthesis
			str[str.length-1] = str[str.length-1].replace(")", ""); // removing right parenthesis

			for (int j=0; j<str.length; j++) {
				if (str[j].startsWith("!")) {
					str[j] = str[j].replace("!","");
					splitKB.add("!"); // adding ! separately to the KB Vector
				}
				splitKB.add(str[j]); // adding all clauses to the KB Vector
			}
			splitKB.add("/");
		}
	}

	// user input for the type to prove
	public static Literal userInput() {

		String user;
		boolean neg = false;
		Literal l;
		System.out.println("\nEnter the type to prove: ");
		user = input.nextLine();
		System.out.println();
		
		if (user.startsWith("!")) {
			neg = true;
			user = user.replace("!","");
		}
		
		l = new Literal(user, neg);
		return l;
	}

	public static void mainApp(Literal l) {
		
		int pos = 0;
		boolean not_clause;
		CNFSubClause[] A = new CNFSubClause[counter];
		CNFClause KB = new CNFClause();

		for (int i=0; i<counter; i++) {
			A[i] = new CNFSubClause();
		}

		for (CNFSubClause s : A) {
			
			if (pos < splitKB.size()) {
				while (!splitKB.get(pos).equals("/")) {
					not_clause = false;
					if (splitKB.get(pos).equals("!")) {
						not_clause = true;
						pos++;
					}
					s.getLiterals().add(new Literal(splitKB.get(pos), not_clause));
					pos++;
				}
				pos++;
			}
		}
		// filling our KB
		for (CNFSubClause s : A) {
			KB.getSubclauses().add(s);
		}
		
        System.out.println("---------------");
        System.out.println();

        // running resolution
        boolean b = PL_Resolution_Bool(KB, l);
        l.print();
        System.out.println("is " + b);

        System.out.println("\nDo you want to see the whole process of the Resolution?\npress Y for yes or any other key for no: ");

        String YorN = yesNo.nextLine();

        if(YorN.equalsIgnoreCase("Y")) {
        	String end = PL_Resolution(KB, l);
        	System.out.println(end);
    	}
	}

	// this resolution algorithm returns true if the type has proven or false if not
    public static boolean PL_Resolution_Bool(CNFClause KB, Literal a) {
        // we create a CNFClause that contains all the clauses of our KB
        CNFClause clauses = new CNFClause();
        clauses.getSubclauses().addAll(KB.getSubclauses());
        
        // and a clause containing the negation of the literal we want to prove
        Literal aCopy = new Literal(a.getName(), !a.getNeg());
        CNFSubClause aClause = new CNFSubClause();
        aClause.getLiterals().add(aCopy);
        clauses.getSubclauses().add(aClause);

        boolean stop = false;
        int step = 1;
        // we will try resolution till either we reach a contradiction or can't produce any new clauses
        while(!stop)
        {
            Vector<CNFSubClause> newsubclauses = new Vector<CNFSubClause>();
            Vector<CNFSubClause> subclauses = clauses.getSubclauses();

            
            step++;
            // for every pair of clauses Ci, Cj
            for(int i = 0; i < subclauses.size(); i++)
            {
                CNFSubClause Ci = subclauses.get(i);

                for(int j = i+1; j < subclauses.size(); j++)
                {
                    CNFSubClause Cj = subclauses.get(j);

                    // we try to apply resolution and we collect any new clauses
                    Vector<CNFSubClause> new_subclauses_for_ci_cj = CNFSubClause.resolution(Ci, Cj);

                    // checking the new subclauses
                    for(int k = 0; k < new_subclauses_for_ci_cj.size(); k++)
                    {
                        CNFSubClause newsubclause = new_subclauses_for_ci_cj.get(k);

                        // if an empty subclause has been generated we have reached contradiction 
                        // and the literal has been proved
                        if(newsubclause.isEmpty()) 
         					return true;
                        
                        
                        // adding all clauses produced that don't exist already
                        if(!(newsubclauses.contains(newsubclause) || clauses.contains(newsubclause)))
                    		newsubclauses.add(newsubclause);
                            
                        
                    }                           
                }
            }
            
            boolean newClauseFound = false;

            // checking if any new clauses were produced
            for(int i = 0; i < newsubclauses.size(); i++)
            {
                if(!clauses.contains(newsubclauses.get(i)))
                {
                    clauses.getSubclauses().addAll(newsubclauses);                    
                    newClauseFound = true;
                }                        
            }

            // if not then the KB does not logically infer the literal we want to prove
            if(!newClauseFound)
            {
                
                stop = true;
            }   
        }
        return false;
    } 

    // this resolution algorithm shows the whole process of the Resolution
    public static String PL_Resolution(CNFClause KB, Literal a) {
        // we create a CNFClause that contains all the clauses of our KB
        CNFClause clauses = new CNFClause();
        clauses.getSubclauses().addAll(KB.getSubclauses());
        
        // and a clause containing the negation of the literal we want to prove
        Literal aCopy = new Literal(a.getName(), !a.getNeg());
        CNFSubClause aClause = new CNFSubClause();
        aClause.getLiterals().add(aCopy);
        clauses.getSubclauses().add(aClause);

        System.out.println("\nWe want to prove: ");
        a.print();

        boolean stop = false;
        int step = 1;
        // we will try resolution till either we reach a contradiction or can't produce any new clauses
        while(!stop)
        {
            Vector<CNFSubClause> newsubclauses = new Vector<CNFSubClause>();
            Vector<CNFSubClause> subclauses = clauses.getSubclauses();

            System.out.println("Step: " + step);
            step++;
            // for every pair of clauses Ci, Cj
            for(int i = 0; i < subclauses.size(); i++)
            {
                CNFSubClause Ci = subclauses.get(i);

                for(int j = i+1; j < subclauses.size(); j++)
                {
                    CNFSubClause Cj = subclauses.get(j);

                    // we try to apply resolution and we collect any new clauses
                    Vector<CNFSubClause> new_subclauses_for_ci_cj = CNFSubClause.resolution(Ci, Cj);

                    // checking the new subclauses
                    for(int k = 0; k < new_subclauses_for_ci_cj.size(); k++)
                    {
                        CNFSubClause newsubclause = new_subclauses_for_ci_cj.get(k);

                        // if an empty subclause has been generated we have reached contradiction 
                        // and the literal has been proved
                        if(newsubclause.isEmpty()) 
                        {   
                            System.out.println("---------------");
                            System.out.println("Resolution between");
                            Ci.print();
                            System.out.println("and");
                            Cj.print();
                            System.out.println("***************");
                            System.out.println("produced:");
                            System.out.println("Empty subclause!!!");
                            return "\nEnd of process";
                        }
                        
                        // adding all clauses produced that don't exist already
                        if(!(newsubclauses.contains(newsubclause) || clauses.contains(newsubclause)))
                        {
                            System.out.println("---------------");
                            System.out.println("Resolution between");
                            Ci.print();
                            System.out.println("and");
                            Cj.print();
                            System.out.println("***************");
                            System.out.println("produced:");
                            newsubclause.print();
                            newsubclauses.add(newsubclause);
                            System.out.println("---------------");
                        }
                    }                           
                }
            }
            
            boolean newClauseFound = false;

            // checking if any new clauses were produced
            for(int i = 0; i < newsubclauses.size(); i++)
            {
                if(!clauses.contains(newsubclauses.get(i)))
                {
                    clauses.getSubclauses().addAll(newsubclauses);                    
                    newClauseFound = true;
                }                        
            }

            // if not then the KB does not logically infer the literal we want to prove
            if(!newClauseFound)
            {
                System.out.println("Not found new clauses");
                stop = true;
            }   
        }
        return "\nEnd of process";
    }    
}   
