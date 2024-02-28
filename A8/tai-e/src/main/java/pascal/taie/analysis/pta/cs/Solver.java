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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.HashSet;
import java.util.Set;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private TaintFlowGraph taintFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        taintFlowGraph = new TaintFlowGraph();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    class TaintFlowGraph {
        private final MultiMap<Pointer, Pointer> successors = Maps.newMultiMap();

        boolean addEdge(Pointer source, Pointer target) {
            return successors.put(source, target);
        }

        Set<Pointer> getSuccsOf(Pointer pointer) {
            return successors.get(pointer);
        }
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        if (callGraph.addReachableMethod(csMethod)) {
            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            CSVar csVar = csManager.getCSVar(context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            CSObj csObj = csManager.getCSObj(contextSelector.selectHeapContext(csMethod, obj), obj);
            PointsToSet pointsToSet = PointsToSetFactory.make(csObj);
            workList.addEntry(csVar, pointsToSet);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            CSVar target = csManager.getCSVar(context, stmt.getLValue());
            CSVar source = csManager.getCSVar(context, stmt.getRValue());
            pointerFlowGraph.addEdge(source, target);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                InvokeExp invokeExp = stmt.getInvokeExp();
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context ct = contextSelector.selectContext(csCallSite, callee);
                CSMethod csMethod = csManager.getCSMethod(ct, callee);
                Edge<CSCallSite, CSMethod> edge = new Edge<>(CallGraphs.getCallKind(stmt), csCallSite, csMethod);
                if (callGraph.addEdge(edge)) {
                    addReachable(csMethod);
                    // c:a_i -> ct:m_pi
                    for (int i = 0; i < invokeExp.getArgCount(); i++) {
                        CSVar source = csManager.getCSVar(context, invokeExp.getArg(i));
                        CSVar target = csManager.getCSVar(ct, callee.getIR().getParam(i));
                        addPFGEdge(source, target);
                    }
                    // ct:m_ret -> c:r
                    if (stmt.getResult() != null) {
                        CSVar target = csManager.getCSVar(context, stmt.getResult());
                        for (Var var : callee.getIR().getReturnVars()) {
                            CSVar source = csManager.getCSVar(ct, var);
                            addPFGEdge(source, target);
                        }
                    }
                }
                // handle taint analysis
                genSourceAndSink(stmt, invokeExp, context, callee, csMethod);
                if (stmt.getResult() != null) {
                    CSVar ret = csManager.getCSVar(context, stmt.getResult());
                    Type type = csMethod.getMethod().getReturnType();
                    for (int i = 0; i < callee.getParamCount(); i++) {
                        if (taintAnalysis.isTaintTransfer(callee, i, -2, type)) {
                            CSVar arg = csManager.getCSVar(context, invokeExp.getArg(i));
                            addTFGEdge(arg, ret);
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
                StaticField staticField = csManager.getStaticField(field);
                CSVar csVar = csManager.getCSVar(context, stmt.getRValue());
                addPFGEdge(csVar, staticField);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                StaticField staticField = csManager.getStaticField(field);
                CSVar csVar = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(staticField, csVar);
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

    private void addTFGEdge(Pointer source, Pointer target) {
        if (taintFlowGraph.addEdge(source, target)) {
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
            if (entry.pointer() instanceof CSVar csVar) {
                Context context = csVar.getContext();
                for (CSObj csObj : delta) {
                    for (LoadField loadField : csVar.getVar().getLoadFields()) {
                        JField field = loadField.getFieldRef().resolve();
                        InstanceField source = csManager.getInstanceField(csObj, field);
                        CSVar target = csManager.getCSVar(context, loadField.getLValue());
                        addPFGEdge(source, target);
                    }
                    for (StoreField storeField : csVar.getVar().getStoreFields()) {
                        JField field = storeField.getFieldRef().resolve();
                        InstanceField target = csManager.getInstanceField(csObj, field);
                        CSVar source = csManager.getCSVar(context, storeField.getRValue());
                        addPFGEdge(source, target);
                    }
                    for (StoreArray storeArray : csVar.getVar().getStoreArrays()) {
                        ArrayIndex target = csManager.getArrayIndex(csObj);
                        CSVar source = csManager.getCSVar(context, storeArray.getRValue());
                        addPFGEdge(source, target);
                    }
                    for (LoadArray loadArray : csVar.getVar().getLoadArrays()) {
                        ArrayIndex source = csManager.getArrayIndex(csObj);
                        CSVar target = csManager.getCSVar(context, loadArray.getLValue());
                        addPFGEdge(source, target);
                    }
                    processCall(csVar, csObj);
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
        PointsToSet delta = PointsToSetFactory.make();
        PointsToSet taintDelta = PointsToSetFactory.make();
        for (CSObj obj : pointsToSet) {
            if (pointer.getPointsToSet().addObject(obj)) {
                delta.addObject(obj);
                if (taintAnalysis.isTaint(obj.getObject())) {
                    taintDelta.addObject(obj);
                }
            }
        }
        if (!delta.isEmpty()) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, delta);
            }
        }
        // propagate taint
        if (!taintDelta.isEmpty()) {
            for (Pointer succ : taintFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, taintDelta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        for (Invoke invoke : recv.getVar().getInvokes()) {
            InvokeExp invokeExp = invoke.getInvokeExp();
            Context context = recv.getContext();
            JMethod callee = resolveCallee(recvObj, invoke);
            if (callee == null) {
                return;
            }
            CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
            Context ct = contextSelector.selectContext(csCallSite, recvObj, callee);
            // recvObj -> m_this
            CSVar pt = csManager.getCSVar(ct, callee.getIR().getThis());
            PointsToSet pts = PointsToSetFactory.make(recvObj);
            workList.addEntry(pt, pts);
            // addEdge
            CSMethod csMethod = csManager.getCSMethod(ct, callee);
            Edge<CSCallSite, CSMethod> edge = new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csMethod);
            if (callGraph.addEdge(edge)) {
                addReachable(csMethod);
                // c:a_i -> ct:m_pi
                for (int i = 0; i < invokeExp.getArgCount(); i++) {
                    CSVar source = csManager.getCSVar(context, invokeExp.getArg(i));
                    CSVar target = csManager.getCSVar(ct, callee.getIR().getParam(i));
                    addPFGEdge(source, target);
                }
                // ct:m_ret -> c:r
                if (invoke.getResult() != null) {
                    CSVar target = csManager.getCSVar(context, invoke.getResult());
                    for (Var var : callee.getIR().getReturnVars()) {
                        CSVar source = csManager.getCSVar(ct, var);
                        addPFGEdge(source, target);
                    }
                }
            }
            // handle taint analysis
            genSourceAndSink(invoke, invokeExp, context, callee, csMethod);
            if (invoke.getResult() != null) {
                CSVar ret = csManager.getCSVar(context, invoke.getResult());
                Type type = csMethod.getMethod().getReturnType();
                for (int i = 0; i < callee.getParamCount(); i++) {
                    // arg -> result
                    if (taintAnalysis.isTaintTransfer(callee, i, -2, type)) {
                        CSVar arg = csManager.getCSVar(context, invokeExp.getArg(i));
                        addTFGEdge(arg, ret);
                    }
                }
                // base -> result
                if (taintAnalysis.isTaintTransfer(callee, -1, -2, type)) {
                    addTFGEdge(recv, ret);
                }
            }
            for (int i = 0; i < callee.getParamCount(); i++) {
                // arg -> base
                Type type = recv.getType();
                if (taintAnalysis.isTaintTransfer(callee, i, -1, type)) {
                    CSVar arg = csManager.getCSVar(context, invokeExp.getArg(i));
                    addTFGEdge(arg, recv);
                }
            }
        }
    }

    public record SinkArg(Invoke invoke, int index, CSVar ai) {}

    private final Set<SinkArg> sinkArgSet = new HashSet<>();

    public Set<SinkArg> getSinkArgSet() {
        return sinkArgSet;
    }

    private void addCGEdge(Invoke invoke, InvokeExp invokeExp, Context context, JMethod callee, CSCallSite csCallSite, Context ct) {

    }

    private void genSourceAndSink(Invoke invoke, InvokeExp invokeExp, Context context, JMethod callee, CSMethod csMethod) {
        if (invoke.getResult() != null) {
            CSVar ret = csManager.getCSVar(context, invoke.getResult());
            Type type = csMethod.getMethod().getReturnType();
            if (taintAnalysis.isSource(callee, type)) {
                MockObj taint = taintAnalysis.getTaint(invoke, type);
                CSObj csTaint = csManager.getCSObj(contextSelector.getEmptyContext(), taint);
                PointsToSet pts = PointsToSetFactory.make(csTaint);
                workList.addEntry(ret, pts);
            }
        }
        for (int i = 0; i < invokeExp.getArgCount(); i++) {
            if (taintAnalysis.isSink(callee, i)) {
                CSVar arg = csManager.getCSVar(context, invokeExp.getArg(i));
                sinkArgSet.add(new SinkArg(invoke, i, arg));
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
