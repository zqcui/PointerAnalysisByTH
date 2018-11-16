package core;

import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.TreeSet;

import soot.Local;
import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.util.queue.QueueReader;
import soot.jimple.InstanceFieldRef;

public class WholeProgramTransformer extends SceneTransformer {

	@Override
	protected void internalTransform(String arg0, Map<String, String> arg1) {

		TreeMap<Integer, Local> queries = new TreeMap<Integer, Local>();
		Anderson anderson = new Anderson();

		ReachableMethods reachableMethods = Scene.v().getReachableMethods();
		QueueReader<MethodOrMethodContext> qr = reachableMethods.listener();
        TreeMap<String,SootMethod> methodMap=new TreeMap<String, SootMethod>() ;//存分析文件中的方法集合


        while (qr.hasNext()) {
            SootMethod sm = qr.next().method();
            if (sm.hasActiveBody()) {
                if (sm.toString().contains("test.FieldSensitivity")) {
                    System.out.println("SootMethod1: " + sm);
                    methodMap.put(sm.toString(), sm);
                }
            }
        }

        qr = reachableMethods.listener();
		while (qr.hasNext()) {
			SootMethod sm = qr.next().method();
			//if (sm.toString().contains("Hello")) {
				int allocId = 0;
				if (sm.hasActiveBody()) {
                    if(sm.toString().contains("test.FieldSensitivity")) {
                        System.out.println("SootMethod2: "+sm);
                        for (Unit u : sm.getActiveBody().getUnits()) {
                            //System.out.println("S: " + u);
                            //System.out.println(u.getClass());
                            if (u instanceof InvokeStmt) {
                                InvokeExpr ie = ((InvokeStmt) u).getInvokeExpr();
                               // System.out.println("instanceof InvokeStmt: "+ie);
                                if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void alloc(int)>")) {
                                    allocId = ((IntConstant)ie.getArgs().get(0)).value;
                                }
                                if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void test(int,java.lang.Object)>")) {
                                    Value v = ie.getArgs().get(1);
                                    int id = ((IntConstant)ie.getArgs().get(0)).value;
                                    queries.put(id, (Local)v);
                                }
                                if(ie.getMethod().toString().equals("<test.FieldSensitivity: void assign(benchmark.objects.A,benchmark.objects.A)>")){
                                    System.out.println("Invoke method:"+ie.toString());
                                    //找到被调用的函数，在形参和实参间addAssignConstraint
                                    SootMethod methodCalled = methodMap.get(ie.getMethod().toString());
                                    System.out.println("SootMethod3: "+methodCalled);
                                    System.out.println("****"+ie.getArg(0));
                                    System.out.println("****"+ie.getArg(1));

                                    System.out.println("****"+methodCalled.getParameterCount());
                                    Local r1 = (Local)methodCalled.getActiveBody().getLocals().toArray()[1];
                                    Local r2 = (Local)methodCalled.getActiveBody().getLocals().toArray()[2];
                                    System.out.println("****"+r1);
                                    System.out.println("****"+r2);


                                    anderson.addAssignConstraint((Local)ie.getArg(0), r1);
                                    anderson.addAssignConstraint((Local)ie.getArg(1), r2);

                                }
                            }
                            if (u instanceof DefinitionStmt) {
                                if (((DefinitionStmt)u).getRightOp() instanceof NewExpr) {
                                    //System.out.println("Alloc " + allocId);
                                    //System.out.println("====new assign====="+"S: "+((DefinitionStmt) u).toString() + "==================");
                                    anderson.addNewConstraint(allocId, (Local)((DefinitionStmt) u).getLeftOp());
                                    //System.out.println("right opr " + ((InstanceFieldRef)(((DefinitionStmt) u).getRightOp())).getField().getName());
                                }
                                if (((DefinitionStmt)u).getLeftOp() instanceof Local && ((DefinitionStmt)u).getRightOp() instanceof Local) {
                                    //System.out.println("==local assign========"+"S: "+((DefinitionStmt) u).toString() + "==================");
                                    anderson.addAssignConstraint((Local)((DefinitionStmt) u).getRightOp(), (Local)((DefinitionStmt) u).getLeftOp());
                                    //System.out.println("right opr " + ((InstanceFieldRef)(((DefinitionStmt) u).getRightOp())).getField().getName());
                                }
                                if (((DefinitionStmt) u).getRightOp() instanceof InstanceFieldRef ) {
                                    System.out.println("Right OP InstanceFieldRef:"+sm.toString());
                                    //System.out.println("=======InstanceFieldRef======"+u.toString()+"=========");
                                    //System.out.println("=====instanceField Right===="+((Local)((InstanceFieldRef)((DefinitionStmt) u).getRightOp()).getBase()).toString() +"======");
                                    //System.out.println("right opr " + ((InstanceFieldRef)(((DefinitionStmt) u).getRightOp())).getField().getName());
                                    //System.out.println("left opr " + ((DefinitionStmt) u).getLeftOp());
                                    if(((DefinitionStmt) u).getLeftOp() instanceof Local){
                                        anderson.addAssignConstraint((Local)((InstanceFieldRef)((DefinitionStmt) u).getRightOp()).getBase(), (Local)((DefinitionStmt) u).getLeftOp());
                                    }
                                    if(((DefinitionStmt) u).getLeftOp() instanceof InstanceFieldRef){
                                        anderson.addAssignConstraint((Local)((InstanceFieldRef)((DefinitionStmt) u).getRightOp()).getBase(), (Local)((InstanceFieldRef)((DefinitionStmt) u).getLeftOp()).getBase());
                                    }
                                }
                            }
                        }
                    }

				}
			//}
		}

		anderson.run();
		String answer = "";
		for (Entry<Integer, Local> q : queries.entrySet()) {
			TreeSet<Integer> result = anderson.getPointsToSet(q.getValue());
			answer += q.getKey().toString() + ":";
			if(result!=null) {
				for (Integer i : result) {
					answer += " " + i;
				}
			}
			answer += "\n";
		}
		AnswerPrinter.printAnswer(answer);

	}

}
