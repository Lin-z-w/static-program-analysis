/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        // unreachable code
        for (Stmt stmt : cfg) {
            deadCode.add(stmt);
        }
        ArrayList<Stmt> reach = new ArrayList<>();
        reach.add(cfg.getEntry());
        int reachSize = 0;
        while (reachSize < reach.size()) {
            Stmt stmt = reach.get(reachSize);
            // System.out.println("stmt: " + stmt.toString());
            deadCode.remove(stmt);
            reachSize++;
            // add reachable
            if (stmt instanceof If ifStmt) {
                ConditionExp cexp = ifStmt.getCondition();
                Value v1 = constants.getInFact(ifStmt).get(cexp.getOperand1());
                Value v2 = constants.getInFact(ifStmt).get(cexp.getOperand2());
                if (v1.isConstant() && v2.isConstant()) {
                    boolean cond = getConditionResult(v1,v2, cexp.getOperator());
                    for (Edge<Stmt> e : cfg.getOutEdgesOf(stmt)) {
                        Stmt succ = e.getTarget();
                        if (!reach.contains(succ)) {
                            if (cond && e.getKind() == Edge.Kind.IF_TRUE) {
                                reach.add(succ);
                            }
                            else if (!cond && e.getKind() == Edge.Kind.IF_FALSE) {
                                reach.add(succ);
                            }
                        }
                    }
                }
                else {
                    addAllSucc(cfg, stmt, reach);
                }
            }
            else if (stmt instanceof SwitchStmt switchStmt) {
                Value condition = constants.getInFact(switchStmt).get(switchStmt.getVar());
                if (condition.isConstant()) {
                    boolean reach_default = true;
                    for (Edge<Stmt> e : cfg.getOutEdgesOf(stmt)) {
                        Stmt succ = e.getTarget();
                        if (e.getKind() == Edge.Kind.SWITCH_CASE) {
                            if (e.getCaseValue() == condition.getConstant()) {
                                reach_default = false;
                                if (!reach.contains(succ)) {
                                    reach.add(succ);
                                }
                            }
                        }
                        else {
                            if (reach_default) {
                                if (!reach.contains(succ)) {
                                    reach.add(succ);
                                }
                            }
                        }
                    }
                    if (reach_default) {
                        reach.add(switchStmt.getDefaultTarget());
                    }
                }
                else {
                    addAllSucc(cfg, stmt, reach);
                }
            }
            else {
                addAllSucc(cfg, stmt, reach);
            }
        }

        // dead assignment
        for (Stmt stmt : reach) {
            // if (cfg.isExit(stmt) || cfg.isEntry(stmt)) continue;
            boolean noSideEffect = true;
            if (stmt instanceof AssignStmt<?,?> assignStmt) {
                for (RValue rValue : assignStmt.getUses()) {
                    noSideEffect &= hasNoSideEffect(rValue);
                }
                if (noSideEffect) {
                    if (assignStmt.getDef().isPresent()) {
                        LValue def = assignStmt.getDef().get();
                        if (def instanceof Var var) {
                            if (!liveVars.getOutFact(assignStmt).contains(var)) {
                                deadCode.add(stmt);
                            }
                        }
                    }
                }
            }
        }

        deadCode.remove(cfg.getEntry());
        deadCode.remove(cfg.getExit());
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }

    private void addAllSucc(CFG<Stmt> cfg, Stmt stmt, ArrayList<Stmt> reach) {
        for (Edge<Stmt> e : cfg.getOutEdgesOf(stmt)) {
            Stmt succ = e.getTarget();
            if (!reach.contains(succ)) {
                reach.add(succ);
            }
        }
    }

    private boolean getConditionResult (Value v1, Value v2, ConditionExp.Op op) {
        boolean result = false;
        switch (op) {
            case NE -> result = (v1.getConstant() != v2.getConstant());
            case LT -> result = (v1.getConstant() < v2.getConstant());
            case LE -> result = (v1.getConstant() <= v2.getConstant());
            case GT -> result = (v1.getConstant() > v2.getConstant());
            case GE -> result = (v1.getConstant() >= v2.getConstant());
            case EQ -> result = (v1.getConstant() == v2.getConstant());
        }
        return result;
    }
}
