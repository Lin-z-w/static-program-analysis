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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.*;
import polyglot.ast.NullLit;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        ArrayList<JMethod> workList = new ArrayList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod tmpMethod = workList.remove(0);
            if (!callGraph.contains(tmpMethod)) {
                callGraph.addReachableMethod(tmpMethod);
                callGraph.callSitesIn(tmpMethod).forEach(cs -> {
                    for (JMethod m : resolve(cs)) {
                        Edge<Invoke, JMethod> edge = new Edge<>(CallGraphs.getCallKind(cs), cs, m);
                        callGraph.addEdge(edge);
                        workList.add(m);
                    }
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature subsignature = methodRef.getSubsignature();
        JClass decClass = methodRef.getDeclaringClass();
        Set<JMethod> result = new HashSet<JMethod>();
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC:
                result.add(decClass.getDeclaredMethod(subsignature));
                break;
            case SPECIAL:
                result.add(dispatch(decClass, subsignature));
                break;
            case VIRTUAL:
            case INTERFACE:
                ArrayList<JClass> subClass = new ArrayList<>();
                subClass.add(decClass);
                while (!subClass.isEmpty()) {
                    JClass tmpClass = subClass.remove(0);
                    if (tmpClass.isInterface()) {
                        subClass.addAll(hierarchy.getDirectSubinterfacesOf(tmpClass));
                        subClass.addAll(hierarchy.getDirectImplementorsOf(tmpClass));
                        JMethod tmp = dispatch(tmpClass, subsignature);
                        if (tmp != null) {
                            result.add(tmp);
                        }
                    }
                    else {
                        subClass.addAll(hierarchy.getDirectSubclassesOf(tmpClass));
                        JMethod tmp = dispatch(tmpClass, subsignature);
                        if (tmp != null) {
                            result.add(tmp);
                        }
                    }
                }
                break;
        }
        return result;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod result = jclass.getDeclaredMethod(subsignature);
        if (result != null && !result.isAbstract()) {
            return result;
        }
        JClass supClass = jclass.getSuperClass();
        if (supClass == null) {
            return null;
        }
        return dispatch(supClass, subsignature);
    }
}
