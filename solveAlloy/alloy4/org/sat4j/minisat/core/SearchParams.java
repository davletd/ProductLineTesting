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

import java.io.Serializable;
import java.lang.reflect.Field;

/**
 * Some parameters used during the search.
 * 
 * @author daniel
 * 
 */
public class SearchParams implements Serializable {

    private static final long serialVersionUID = 1L;

    /**
     * Default search parameters.
     *
     */
    public SearchParams() {
        this(0.95, 0.999, 1.5, 100);
    }

    /** 
     * 
     * @param conflictBound the initial conflict bound for the first restart.
     */
    public SearchParams(int conflictBound) {
        this(0.95, 0.999, 1.5, conflictBound);
    }

    public SearchParams(double confincfactor, int conflictBound) {
        this(0.95, 0.999, confincfactor, conflictBound);
    }

    /**
     * @param d
     *            variable decay
     * @param e
     *            clause decay
     * @param f
     *            conflict bound increase factor
     * @param i
     *            initialConflictBound
     */
    public SearchParams(double d, double e, double f, int i) {
        varDecay = d;
        claDecay = e;
        conflictBoundIncFactor = f;
        initConflictBound = i;
    }

    /**
     * @return la valeur de clause decay
     */
    public double getClaDecay() {
        return claDecay;
    }

    /**
     * @return la valeur de var decay
     */
    public double getVarDecay() {
        return varDecay;
    }

    private double claDecay;

    private double varDecay;

    private double conflictBoundIncFactor;

    private int initConflictBound;

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuffer stb = new StringBuffer();
        for (Field field : SearchParams.class.getDeclaredFields()) {
            if (!field.getName().startsWith("serial")) {
                stb.append(field.getName());
                stb.append("="); //$NON-NLS-1$
                try {
                    stb.append(field.get(this));
                } catch (IllegalArgumentException e) {
                    e.printStackTrace();
                } catch (IllegalAccessException e) {
                    e.printStackTrace();
                }
                stb.append(" "); //$NON-NLS-1$
            }
        }
        return stb.toString();
    }

    /**
     * @param conflictBoundIncFactor
     *            the conflictBoundIncFactor to set
     */
    public void setConflictBoundIncFactor(double conflictBoundIncFactor) {
        this.conflictBoundIncFactor = conflictBoundIncFactor;
    }

    /**
     * @param initConflictBound
     *            the initConflictBound to set
     */
    public void setInitConflictBound(int initConflictBound) {
        this.initConflictBound = initConflictBound;
    }

    /**
     * @return the conflictBoundIncFactor
     */
    public double getConflictBoundIncFactor() {
        return conflictBoundIncFactor;
    }

    /**
     * @return the initConflictBound
     */
    public int getInitConflictBound() {
        return initConflictBound;
    }

    /**
     * @param claDecay
     *            the claDecay to set
     */
    public void setClaDecay(double claDecay) {
        this.claDecay = claDecay;
    }

    /**
     * @param varDecay
     *            the varDecay to set
     */
    public void setVarDecay(double varDecay) {
        this.varDecay = varDecay;
    }
}
