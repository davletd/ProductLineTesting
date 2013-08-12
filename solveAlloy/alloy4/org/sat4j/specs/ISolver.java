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
package org.sat4j.specs;

import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.Serializable;
import java.util.Map;

/**
 * That interface contains all the services available on a SAT solver.
 * 
 * @author leberre
 */
public interface ISolver extends IProblem, Serializable {

    /**
     * Create a new variable in the solver (and thus in the vocabulary).
     * 
     * WE STRONGLY ENCOURAGE TO PRECOMPUTE THE NUMBER OF VARIABLES NEEDED AND TO
     * USE newVar(howmany) INSTEAD. IF YOU EXPERIENCE A PROBLEM OF EFFICIENCY
     * WHEN READING/BUILDING YOUR SAT INSTANCE, PLEASE CHECK THAT YOU ARE NOT
     * USING THAT METHOD.
     * 
     * @return the number of variables available in the vocabulary, which is the
     *         identifier of the new variable.
     */
    @Deprecated
    int newVar();

    /**
     * Create <code>howmany</code> variables in the solver (and thus in the
     * vocabulary).
     * 
     * @param howmany
     *            number of variables to create
     * @return the total number of variables available in the solver (the
     *         highest variable number)
     */
    int newVar(int howmany);

    /**
     * To inform the solver of the expected number of clauses to read. This is
     * an optional method, that is called when the <code>p cnf</code> line is
     * read in dimacs formatted input file.
     * 
     * Note that this method is supposed to be called AFTER a call to newVar(int)
     * 
     * @param nb
     *            the expected number of clauses.
     * @see #newVar(int)
     * @since 1.6
     */
    void setExpectedNumberOfClauses(int nb);

    /**
     * Create a clause from a set of literals The literals are represented by
     * non null integers such that opposite literals a represented by opposite
     * values. (classical Dimacs way of representing literals).
     * 
     * @param literals
     *            a set of literals
     * @return a reference to the constraint added in the solver, to use in
     *         removeConstr().
     * @throws ContradictionException
     *             iff the vector of literals is empty or if it contains only
     *             falsified literals after unit propagation
     * @see #removeConstr(IConstr)
     */
    IConstr addClause(IVecInt literals) throws ContradictionException;

    /**
     * Remove a constraint returned by one of the add method from the solver.
     * All learned clauses will be cleared.
     * 
     * @param c
     *            a constraint returned by one of the add method.
     * @return true if the constraint was successfully removed.
     */
    boolean removeConstr(IConstr c);

    /**
     * Create clauses from a set of set of literals. This is convenient to
     * create in a single call all the clauses (mandatory for the distributed
     * version of the solver). It is mainly a loop to addClause().
     * 
     * @param clauses
     *            a vector of set (VecInt) of literals in the dimacs format. The
     *            vector can be reused since the solver is not supposed to keep
     *            a reference to that vector.
     * @throws ContradictionException
     *             iff the vector of literals is empty or if it contains only
     *             falsified literals after unit propagation
     * @see #addClause(IVecInt)
     */
    void addAllClauses(IVec<IVecInt> clauses) throws ContradictionException;

    /**
     * Create a cardinality constraint of the type "at most n of those literals
     * must be satisfied"
     * 
     * @param literals
     *            a set of literals The vector can be reused since the solver is
     *            not supposed to keep a reference to that vector.
     * @param degree
     *            the degree of the cardinality constraint
     * @return a reference to the constraint added in the solver, to use in
     *         removeConstr().
     * @throws ContradictionException
     *             iff the vector of literals is empty or if it contains more
     *             than degree satisfied literals after unit propagation
     * @see #removeConstr(IConstr)
     */

    IConstr addAtMost(IVecInt literals, int degree)
            throws ContradictionException;

    /**
     * Create a cardinality constraint of the type "at least n of those literals
     * must be satisfied"
     * 
     * @param literals
     *            a set of literals. The vector can be reused since the solver
     *            is not supposed to keep a reference to that vector.
     * @param degree
     *            the degree of the cardinality constraint
     * @return a reference to the constraint added in the solver, to use in
     *         removeConstr().
     * @throws ContradictionException
     *             iff the vector of literals is empty or if degree literals are
     *             not remaining unfalsified after unit propagation
     * @see #removeConstr(IConstr)
     */
    IConstr addAtLeast(IVecInt literals, int degree)
            throws ContradictionException;

    /**
     * To set the internal timeout of the solver. When the timeout is reached, a
     * timeout exception is launched by the solver.
     * 
     * @param t
     *            the timeout (in s)
     */
    void setTimeout(int t);

    /**
     * To set the internal timeout of the solver. When the timeout is reached, a
     * timeout exception is launched by the solver.
     * 
     * Here the timeout is given in number of conflicts. That way, the behavior 
     * of the solver should be the same across different architecture.
     * 
     * @param count
     *            the timeout (in number of counflicts)
     */
    void setTimeoutOnConflicts(int count);
    
    /**
     * To set the internal timeout of the solver. When the timeout is reached, a
     * timeout exception is launched by the solver.
     * 
     * @param t
     *            the timeout (in milliseconds)
     */
    void setTimeoutMs(long t);
    
    /**
     * Useful to check the internal timeout of the solver.
     * 
     * @return the internal timeout of the solver (in second)
     */
    int getTimeout();

    /**
     * Expire the timeout of the solver.
     */
    void expireTimeout();

    /**
     * Clean up the internal state of the solver.
     */
    void reset();

    /**
     * Display statistics to the given output stream Please use writers instead
     * of stream.
     * 
     * @param out
     * @param prefix
     *            the prefix to put in front of each line
     * @see #printStat(PrintWriter, String)
     */
    @Deprecated
    void printStat(PrintStream out, String prefix);

    /**
     * Display statistics to the given output writer
     * 
     * @param out
     * @param prefix
     *            the prefix to put in front of each line
     * @since 1.6
     */
    void printStat(PrintWriter out, String prefix);

    /**
     * To obtain a map of the available statistics from the solver. Note that
     * some keys might be specific to some solvers.
     * 
     * @return a Map with the name of the statistics as key.
     */
    Map<String, Number> getStat();

    /**
     * Display a textual representation of the solver configuration.
     * 
     * @param prefix
     *            the prefix to use on each line.
     * @return a textual description of the solver internals.
     */
    String toString(String prefix);

    void clearLearntClauses();
}
