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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static java.lang.System.exit;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
    public Context getEmptyContext() {
        return emptyContext;
    }

    public boolean isSource(JMethod jMethod, Type type) {
        return config.getSources().contains(new Source(jMethod, type));
    }

    public MockObj getTaint(Invoke invoke, Type type) {
        return (MockObj) manager.makeTaint(invoke, type);
    }

    public boolean isSink(JMethod jMethod, int i) {
        return config.getSinks().contains(new Sink(jMethod, i));
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    public boolean isTaintTransfer(JMethod method, int from, int to, Type type) {
        return config.getTransfers().contains(new TaintTransfer(method, from, to, type));
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        Set<Solver.SinkArg> sinkArgSet = solver.getSinkArgSet();
        for (Solver.SinkArg s : sinkArgSet) {
            Set<CSObj> objs = result.getPointsToSet(s.ai());
            for (CSObj csObj : objs) {
                if (manager.isTaint(csObj.getObject())) {
                    TaintFlow taintFlow = new TaintFlow(manager.getSourceCall(csObj.getObject()), s.invoke(), s.index());
                    taintFlows.add(taintFlow);
                }
            }
        }
        return taintFlows;
    }
}
