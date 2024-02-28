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

package pascal.taie.analysis.dataflow.inter;

        import pascal.taie.World;
        import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
        import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
        import pascal.taie.analysis.dataflow.analysis.constprop.Value;
        import pascal.taie.analysis.graph.cfg.CFGBuilder;
        import pascal.taie.analysis.graph.icfg.CallEdge;
        import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
        import pascal.taie.analysis.graph.icfg.NormalEdge;
        import pascal.taie.analysis.graph.icfg.ReturnEdge;
        import pascal.taie.analysis.pta.PointerAnalysisResult;
        import pascal.taie.analysis.pta.core.heap.Obj;
        import pascal.taie.config.AnalysisConfig;
        import pascal.taie.ir.IR;
        import pascal.taie.ir.exp.*;
        import pascal.taie.ir.stmt.*;
        import pascal.taie.language.classes.JMethod;
        import pascal.taie.util.collection.SetQueue;

        import java.util.*;
        import java.util.stream.Collectors;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private Map<LoadField, Set<StoreField>> insFieldAlias, staFieldAlias;

    private Map<LoadArray, Set<StoreArray>> possibleArrayAlias;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        Queue<StoreField> insStoreFieldList = new SetQueue<>(), staStoreFieldList = new SetQueue<>();
        Queue<LoadField> insLoadFieldList = new SetQueue<>(), staLoadFieldList = new SetQueue<>();
        Queue<LoadArray> loadArrays = new SetQueue<>();
        Queue<StoreArray> storeArrays = new SetQueue<>();
        for (Stmt stmt : icfg) {
            if (stmt instanceof LoadField loadField) {
                if (loadField.isStatic()) {
                    staLoadFieldList.add(loadField);
                }
                else {
                    insLoadFieldList.add(loadField);
                }
            }
            else if (stmt instanceof StoreField storeField) {
                if (storeField.isStatic()) {
                    staStoreFieldList.add(storeField);
                }
                else {
                    insStoreFieldList.add(storeField);
                }
            }
            else if (stmt instanceof LoadArray loadArray) {
                loadArrays.add(loadArray);
            }
            else if (stmt instanceof StoreArray storeArray) {
                storeArrays.add(storeArray);
            }
        }
        insFieldAlias = new HashMap<>();
        for (LoadField loadField : insLoadFieldList) {
            Set<StoreField> storeSet = new HashSet<>();
            insFieldAlias.put(loadField, storeSet);
            for (StoreField storeField : insStoreFieldList) {
                // is alias
                if (isFieldAlias(loadField, storeField, pta)) {
                    insFieldAlias.get(loadField).add(storeField);
                }
            }
        }
        staFieldAlias = new HashMap<>();
        for (LoadField loadField : staLoadFieldList) {
            Set<StoreField> storeSet = new HashSet<>();
            staFieldAlias.put(loadField, storeSet);
            for (StoreField storeField : staStoreFieldList) {
                // the same field
                if (loadField.getFieldRef().resolve().equals(storeField.getFieldRef().resolve())) {
                    staFieldAlias.get(loadField).add(storeField);
                }
            }
        }
        possibleArrayAlias = new HashMap<>();
        for (LoadArray loadArray : loadArrays) {
            Set<StoreArray> storeSet = new HashSet<>();
            possibleArrayAlias.put(loadArray, storeSet);
            for (StoreArray storeArray : storeArrays) {
                if (maybeArrayAlias(loadArray, storeArray, pta)) {
                    possibleArrayAlias.get(loadArray).add(storeArray);
                }
            }
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return identityTrandfer(in, out);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean change;
        if (stmt instanceof LoadField loadField) {
            if (loadField.isStatic()) {
                change = transferLoadField(loadField, in, out, staFieldAlias);
            }
            else {
                change = transferLoadField(loadField, in, out, insFieldAlias);
            }
        }
        else if (stmt instanceof StoreField storeField) {
            change = identityTrandfer(in, out);
            if (change) {
                if (storeField.isStatic()) {
                    for (LoadField l : staFieldAlias.keySet()) {
                        if (staFieldAlias.get(l).contains(storeField)) {
                            solver.addWorkList(l);
                        }
                    }
                }
                else {
                    for (LoadField l : insFieldAlias.keySet()) {
                        if (insFieldAlias.get(l).contains(storeField)) {
                            solver.addWorkList(l);
                        }
                    }
                }
            }
        }
        else if (stmt instanceof LoadArray loadArray) {
            change = transferLoadArray(loadArray, in, out);
        }
        else if (stmt instanceof StoreArray storeArray) {
            change = identityTrandfer(in, out);
            if (change) {
                for (LoadArray l : possibleArrayAlias.keySet()) {
                    if (possibleArrayAlias.get(l).contains(storeArray)) {
                        solver.addWorkList(l);
                    }
                }
            }
        }
        else {
            change = cp.transferNode(stmt, in, out);
        }
        return change;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Stmt source = edge.getSource();
        CPFact newOut = out.copy();
        if (source.getDef().isPresent()) {
            LValue def = source.getDef().get();
            if (def instanceof Var var) {
                newOut.remove(var);
            }
        }
        return newOut;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        JMethod callee = edge.getCallee();
        Stmt source = edge.getSource();
        CPFact result = new CPFact();
        for (RValue r : source.getUses()) {
            if (r instanceof InvokeExp invokeExp) {
                List<Var> args = invokeExp.getArgs();
                List<Var> para = callee.getIR().getParams();
                for (int i = 0; i < para.size(); i++) {
                    result.update(para.get(i), callSiteOut.get(args.get(i)));
                }
            }
        }
        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        Stmt callSite = edge.getCallSite();
        CPFact result = new CPFact();
        Collection<Var> returnVar =  edge.getReturnVars();
        Value returnValue = null;
        for (Var v : returnVar) {
            if (returnValue == null) {
                returnValue = returnOut.get(v);
            }
            else {
                returnValue = cp.meetValue(returnValue, returnOut.get(v));
            }
        }
        if (callSite instanceof Invoke invoke) {
            if (invoke.getResult() != null && returnValue != null) {
                result.update(invoke.getResult(), returnValue);
            }
        }
        return result;
    }

    // helper function
    private boolean transferLoadField(LoadField loadField, CPFact in, CPFact out, Map<LoadField, Set<StoreField>> aliasMap) {
        boolean change = identityTrandfer(in, out);
        for (StoreField storeField : aliasMap.get(loadField)) {
            Value storeValue = ConstantPropagation.evaluate(storeField.getRValue(), solver.getNodeInFact(storeField));
            Var def = loadField.getLValue();
            storeValue = cp.meetValue(out.get(def), storeValue);
            if (ConstantPropagation.canHoldInt(def)) {
                change |= out.update(def, storeValue);
            }
        }
        return change;
    }

    private boolean transferLoadArray(LoadArray loadArray, CPFact in, CPFact out) {
        boolean change = identityTrandfer(in, out);
        for (StoreArray storeArray : possibleArrayAlias.get(loadArray)) {
            if (isArrayAlias(loadArray, storeArray)) {
                Value storeValue = ConstantPropagation.evaluate(storeArray.getRValue(), solver.getNodeInFact(storeArray));
                Var def = loadArray.getLValue();
                storeValue = cp.meetValue(out.get(def), storeValue);
                if (ConstantPropagation.canHoldInt(def)) {
                    change |= out.update(def, storeValue);
                }
            }
        }
        return change;
    }

    private boolean isFieldAlias(LoadField load, StoreField store, PointerAnalysisResult pta) {
        FieldAccess loadfieldAccess = load.getFieldAccess();
        FieldAccess storeFieldAccess = store.getFieldAccess();
        Var loadBase = null, storeBase = null;
        if (loadfieldAccess instanceof InstanceFieldAccess) {
            loadBase = ((InstanceFieldAccess) loadfieldAccess).getBase();
        }
        if (storeFieldAccess instanceof InstanceFieldAccess) {
            storeBase = ((InstanceFieldAccess) storeFieldAccess).getBase();
        }
        Set<Obj> loadPts = pta.getPointsToSet(loadBase), storePts = pta.getPointsToSet(storeBase);
        // weather base has intersection
        boolean res = intersect(loadPts, storePts);
        if (res) {
            // weather visit the same field
            if (load.getFieldRef().resolve().equals(store.getFieldRef().resolve())) {
                return res;
            }
        }
        return false;
    }

    private boolean maybeArrayAlias(LoadArray load, StoreArray store, PointerAnalysisResult pta) {
        ArrayAccess laa = load.getArrayAccess(), saa = store.getArrayAccess();
        Var loadBase = laa.getBase(), storeBase = saa.getBase();
        return intersect(pta.getPointsToSet(loadBase), pta.getPointsToSet(storeBase));
    }

    private boolean isArrayAlias(LoadArray load, StoreArray store) {
        Var loadIndex = load.getArrayAccess().getIndex(), storeIndex = store.getArrayAccess().getIndex();
        Value liValue = ConstantPropagation.evaluate(loadIndex, solver.getNodeInFact(load));
        Value siValue = ConstantPropagation.evaluate(storeIndex, solver.getNodeInFact(store));
        if (liValue.isUndef() || siValue.isUndef()) {
            return false;
        }
        else if (liValue.isConstant() && siValue.isConstant()) {
            return liValue.getConstant() == siValue.getConstant();
        }
        return true;
    }
    private boolean intersect(Set<Obj> s1, Set<Obj> s2) {
        Set<Obj> intersect = s1.stream().filter(s2::contains).collect(Collectors.toSet());
        return !intersect.isEmpty();
    }

    private boolean identityTrandfer(CPFact in, CPFact out) {
        boolean change = false;
        for (Var key : in.keySet()) {
            change |= out.update(key, in.get(key));
        }
        return change;
    }
}