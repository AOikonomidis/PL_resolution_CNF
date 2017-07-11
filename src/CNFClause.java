/*

 	@authors: Andrew Oikonomidis & Andronikos Koutroumpelis

 */

import java.util.Vector;


 // a CNFClause consists of a conjunction of CNFSubClauses
public class CNFClause {
	
    public Vector<CNFSubClause> theClauses = new Vector<CNFSubClause>();
    
    public Vector<CNFSubClause> getSubclauses() {
        return theClauses;
    }
    
    public boolean contains(CNFSubClause newS) {
        for(int i = 0; i < theClauses.size(); i ++) {
            if(theClauses.get(i).getLiterals().equals(newS.getLiterals())) {
                return true;
            }
        }
        return false;
    }
}
