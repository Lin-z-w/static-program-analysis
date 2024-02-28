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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import javax.crypto.spec.PSource;
import java.awt.*;
import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            for (Stmt stmt : method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            Pointer pt = pointerFlowGraph.getVarPtr(stmt.getLValue());
            PointsToSet pointsToSet = new PointsToSet(heapModel.getObj(stmt));
            workList.addEntry(pt, pointsToSet);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            VarPtr source = pointerFlowGraph.getVarPtr(stmt.getRValue());
            VarPtr target = pointerFlowGraph.getVarPtr(stmt.getLValue());
            addPFGEdge(source, target);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                InvokeExp invokeExp = stmt.getInvokeExp();
                VarPtr source, target;
                // add edge l->m
                Edge<Invoke, JMethod> edge = new Edge<>(CallGraphs.getCallKind(stmt), stmt, callee);
                if (callGraph.addEdge(edge)) {
                    addReachable(callee);
                    for (int i = 0; i < invokeExp.getArgs().size(); i++) {
                        source = pointerFlowGraph.getVarPtr(invokeExp.getArg(i));
                        target = pointerFlowGraph.getVarPtr(callee.getIR().getParam(i));
                        addPFGEdge(source, target);
                    }
                    // m_ret -> r
                    if (stmt.getResult() != null) {
                        target = pointerFlowGraph.getVarPtr(stmt.getResult());
                        for (Var var : callee.getIR().getReturnVars()) {
                            source = pointerFlowGraph.getVarPtr(var);
                            addPFGEdge(source, target);
                        }
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                StaticField staticField = pointerFlowGraph.getStaticField(field);
                VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(varPtr, staticField);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                StaticField staticField = pointerFlowGraph.getStaticField(field);
                VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                addPFGEdge(staticField, varPtr);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            if (entry.pointer() instanceof VarPtr varPtr) {
                for (Obj obj : delta) {
                    for (LoadField loadField: varPtr.getVar().getLoadFields()) {
                        InstanceField source = pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve());
                        VarPtr target = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        addPFGEdge(source, target);
                    }
                    for (StoreField storeField: varPtr.getVar().getStoreFields()) {
                        InstanceField target = pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve());
                        VarPtr source = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        addPFGEdge(source, target);
                    }
                    for (StoreArray storeArray: varPtr.getVar().getStoreArrays()) {
                        ArrayIndex target = pointerFlowGraph.getArrayIndex(obj);
                        VarPtr source = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        addPFGEdge(source, target);
                    }
                    for (LoadArray loadArray: varPtr.getVar().getLoadArrays()) {
                        ArrayIndex source = pointerFlowGraph.getArrayIndex(obj);
                        VarPtr target = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        addPFGEdge(source, target);
                    }
                    processCall(varPtr.getVar(), obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        // calculate delta
        PointsToSet delta = new PointsToSet();
        for (Obj obj : pointsToSet) {
            if (pointer.getPointsToSet().addObject(obj)) {
                delta.addObject(obj);
            }
        }
        for (Obj obj : delta) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke invoke : var.getInvokes()) {
            JMethod callee = resolveCallee(recv, invoke);
            Pointer pt = pointerFlowGraph.getVarPtr(callee.getIR().getThis());
            PointsToSet pts = new PointsToSet(recv);
            workList.addEntry(pt, pts);
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, callee))) {
                addReachable(callee);
                for (int i = 0; i < callee.getIR().getParams().size(); i++) {
                    VarPtr source = pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i));
                    VarPtr target = pointerFlowGraph.getVarPtr(callee.getIR().getParam(i));
                    addPFGEdge(source, target);
                }
                // m_ret -> result
                if (invoke.getResult() != null) {
                    VarPtr target = pointerFlowGraph.getVarPtr(invoke.getResult());
                    for (Var ret : callee.getIR().getReturnVars()) {
                        VarPtr source = pointerFlowGraph.getVarPtr(ret);
                        addPFGEdge(source, target);
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
