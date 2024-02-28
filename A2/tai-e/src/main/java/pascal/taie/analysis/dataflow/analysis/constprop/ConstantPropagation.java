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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Map;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact cpFact = new CPFact();
        for (Var var: cfg.getIR().getParams()) {
            if (canHoldInt(var)) {
                cpFact.update(var, Value.getNAC());
            }
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var key : target.keySet()) {
            target.update(key, meetValue(target.get(key), fact.get(key)));
        }
        for (Var key : fact.keySet()) {
            target.update(key, meetValue(target.get(key), fact.get(key)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        Value result;
        if (v1.isNAC() || v2.isNAC()) {
            result = Value.getNAC();
        }
        else if (v1.isUndef()) {
            result = v2;
        }
        else if (v2.isUndef()) {
            result = v1;
        }
        else {
            if (v1.equals(v2)) {
                result = v1;
            }
            else {
                result = Value.getNAC();
            }
        }
        return result;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean change = false;
        for (Var key : in.keySet()) {
            change |= out.update(key, in.get(key));
        }
        if (stmt instanceof DefinitionStmt<?,?>) {
            Value expValue = evaluate(((DefinitionStmt<?,?>) stmt).getRValue(), in);
            if (stmt.getDef().isPresent()) {
                LValue def = stmt.getDef().get();
                if (def instanceof Var) {
                    if (canHoldInt((Var) def)) {
                        change |= out.update((Var) def, expValue);
                    }
                }
            }
        }
        return change;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        Value result;
        if (exp instanceof Var) {
            result = evaluateVar((Var) exp, in);
        }
        else if (exp instanceof IntLiteral) {
            result = evaluateIntLiteral((IntLiteral) exp);
        }
        else if (exp instanceof BinaryExp) {
            result = evaluateBinaryExp((BinaryExp) exp, in);
        }
        else {
            result = Value.getNAC();
        }
        return result;
    }
    private static Value evaluateVar(Var var, CPFact in) {
        int value;
        Value result;
        Value op = in.get(var);
        if (op.isUndef()) {
            result = Value.getUndef();
        }
        else if (op.isNAC()) {
            result = Value.getNAC();
        }
        else {
            value = op.getConstant();
            result = Value.makeConstant(value);
        }
        return result;
    }

    private static Value evaluateIntLiteral(IntLiteral intLiteral) {
        return Value.makeConstant(intLiteral.getValue());
    }

    private static Value evaluateBinaryExp(BinaryExp binaryExp, CPFact in) {
        Value result = Value.getNAC(), op1 = in.get(binaryExp.getOperand1()), op2 = in.get(binaryExp.getOperand2());
        // div zero
        if (binaryExp instanceof ArithmeticExp &&
                (((ArithmeticExp) binaryExp).getOperator() == ArithmeticExp.Op.REM || ((ArithmeticExp) binaryExp).getOperator() == ArithmeticExp.Op.DIV) &&
                op2.isConstant() && op2.getConstant() == 0) {
            return Value.getUndef();
        }
        if (op1.isConstant() && op2.isConstant()) {
            if (binaryExp instanceof ArithmeticExp) {
                switch (((ArithmeticExp) binaryExp).getOperator()) {
                    case ADD -> result = Value.makeConstant(op1.getConstant() + op2.getConstant());
                    case SUB -> result = Value.makeConstant(op1.getConstant() - op2.getConstant());
                    case DIV -> result = Value.makeConstant(op1.getConstant() / op2.getConstant());
                    case MUL -> result = Value.makeConstant(op1.getConstant() * op2.getConstant());
                    case REM -> result = Value.makeConstant(op1.getConstant() % op2.getConstant());

                }
            }
            else if (binaryExp instanceof ConditionExp) {
                switch (((ConditionExp) binaryExp).getOperator()) {
                    case EQ -> result = Value.makeConstant(boolToInt(op1.getConstant() == op2.getConstant()));
                    case GE -> result = Value.makeConstant(boolToInt(op1.getConstant() >= op2.getConstant()));
                    case GT -> result = Value.makeConstant(boolToInt(op1.getConstant() > op2.getConstant()));
                    case LE -> result = Value.makeConstant(boolToInt(op1.getConstant() <= op2.getConstant()));
                    case LT -> result = Value.makeConstant(boolToInt(op1.getConstant() < op2.getConstant()));
                    case NE -> result = Value.makeConstant(boolToInt(op1.getConstant() != op2.getConstant()));
                }
            }
            else if (binaryExp instanceof ShiftExp) {
                switch (((ShiftExp) binaryExp).getOperator()) {
                    case SHL -> result = Value.makeConstant(op1.getConstant() << op2.getConstant());
                    case SHR -> result = Value.makeConstant(op1.getConstant() >> op2.getConstant());
                    case USHR -> result = Value.makeConstant(op1.getConstant() >>> op2.getConstant());
                }
            }
            else if (binaryExp instanceof BitwiseExp) {
                switch (((BitwiseExp) binaryExp).getOperator()) {
                    case OR -> result = Value.makeConstant(op1.getConstant() | op2.getConstant());
                    case AND -> result = Value.makeConstant(op1.getConstant() & op2.getConstant());
                    case XOR -> result = Value.makeConstant(op1.getConstant() ^ op2.getConstant());
                }
            }
        }
        else if (op1.isNAC() || op2.isNAC()) {
            result = Value.getNAC();
        }
        else {
            result = Value.getUndef();
        }
        return result;
    }

    private static int boolToInt(boolean b) {
        if (b) return 1;
        return 0;
    }
}
