/*******************************************************************************
* SAT4J: a SATisfiability library for Java Copyright (C) 2004-2008 Daniel Le Berre
*
* All rights reserved. This program and the accompanying materials
* are made available under the terms of the Eclipse Public License v1.0
* which accompanies this distribution, and is available at
* http://www.eclipse.org/legal/epl-v10.html
*
* Alternatively, the contents of this file may be used under the terms of
* either the GNU Lesser General Public License Version 2.1 or later (the
* "LGPL"), in which case the provisions of the LGPL are applicable instead
* of those above. If you wish to allow use of your version of this file only
* under the terms of the LGPL, and not to allow others to use your version of
* this file under the terms of the EPL, indicate your decision by deleting
* the provisions above and replace them with the notice and other provisions
* required by the LGPL. If you do not delete the provisions above, a recipient
* may use your version of this file under the terms of the EPL or the LGPL.
* 
* Based on the original MiniSat specification from:
* 
* An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
* Sixth International Conference on Theory and Applications of Satisfiability
* Testing, LNCS 2919, pp 502-518, 2003.
*
* See www.minisat.se for the original solver in C++.
* 
*******************************************************************************/
package org.sat4j.minisat.core;

import java.io.PrintWriter;

/**
 * Interface for the variable ordering heuristics. It has both the
 * responsibility to choose the next variable to branch on and the phase of the
 * literal (positive or negative one).
 * 
 * @author daniel
 * 
 */
public interface IOrder<L extends ILits> {

    /**
     * Method used to provide an easy access the the solver vocabulary.
     * 
     * @param lits
     *            the vocabulary
     */
    void setLits(L lits);

    /**
     * Method called each time Solver.newVar() is called.
     * 
     */
    @Deprecated
    void newVar();

    /**
     * Method called when Solver.newVar(int) is called.
     * 
     * @param howmany
     *            the maximum number of variables
     * @see Solver#newVar(int)
     */
    void newVar(int howmany);

    /**
     * Selects the next "best" unassigned literal.
     * 
     * Note that it means selecting the best variable and the phase to branch on
     * first.
     * 
     * @return an unassigned literal or Lit.UNDEFINED no such literal exists.
     */
    int select();

    /**
     * Method called when a variable is unassigned.
     * 
     * It is useful to add back a variable in the pool of variables to order.
     * 
     * @param x
     *            a variable.
     */
    void undo(int x);

    /**
     * To be called when the activity of a literal changed.
     * 
     * @param p
     *            a literal. The associated variable will be updated.
     */
    void updateVar(int p);

    /**
     * that method has the responsibility to initialize all arrays in the
     * heuristics. PLEASE CALL super.init() IF YOU OVERRIDE THAT METHOD.
     */
    void init();

    /**
     * Display statistics regarding the heuristics.
     * 
     * @param out
     *            the writer to display the information in
     * @param prefix
     *            to be used in front of each newline.
     */
    void printStat(PrintWriter out, String prefix);

    /**
     * Sets the variable activity decay as a growing factor for the next
     * variable activity.
     * 
     * @param d
     *            a number bigger than 1 that will increase the activity of the
     *            variables involved in future conflict. This is similar but
     *            more efficient than decaying all the activities by a similar
     *            factor.
     */
    void setVarDecay(double d);

    /**
     * Decay the variables activities.
     * 
     */
    void varDecayActivity();

    /**
     * To obtain the current activity of a variable.
     * 
     * @param p
     *            a literal
     * @return the activity of the variable associated to that literal.
     */
    double varActivity(int p);
    
    /**
     * indicate that a literal has been satisfied.
     * 
     * @param p
     */
    void assignLiteral(int p);
    
    void setPhaseSelectionStrategy(IPhaseSelectionStrategy strategy);
    
    IPhaseSelectionStrategy getPhaseSelectionStrategy();
}
