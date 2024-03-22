/*
Aircraft Landing Problem
 */
package alp;

import gnu.trove.map.hash.TObjectIntHashMap;
import static java.lang.Runtime.getRuntime;
import org.kohsuke.args4j.Option;
import org.chocosolver.samples.AbstractProblem;
import org.chocosolver.solver.ResolutionPolicy;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.constraints.IntConstraintFactory;
import org.chocosolver.solver.constraints.LogicalConstraintFactory;
import org.chocosolver.solver.constraints.ternary.Max;
import org.chocosolver.solver.search.limits.FailCounter;
import org.chocosolver.solver.search.loop.lns.LNSFactory;
import org.chocosolver.solver.search.loop.monitors.SMF;
import org.chocosolver.solver.search.strategy.IntStrategyFactory;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.VariableFactory;
import org.chocosolver.util.ESat;


import java.util.*;
import java.util.regex.Pattern;
import static org.chocosolver.samples.AbstractProblem.Level.QUIET;
import static org.chocosolver.samples.AbstractProblem.Level.SILENT;
import org.chocosolver.solver.explanations.ExplanationFactory;
import org.chocosolver.solver.search.loop.monitors.IMonitorSolution;
import org.chocosolver.solver.trace.Chatterbox;
import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.CmdLineParser;

/**
 * "Given a set of planes and runways, the objective is to minimize the total (weighted) deviation from
 * the target landing time for each plane.
 *
 * @author 
 */
public class ALP {
   public static boolean exectuting=false;    
   private int runways=1;
   public enum Level {
        SILENT(-10), QUIET(0), VERBOSE(10), SOLUTION(20), SEARCH(30);
        int level;
        Level(int level) {
            this.level = level;
        }
        public int getLevel() {
            return level;
        }
    }

    protected Level level = Level.SOLUTION;
    protected long seed = 29091981;//29091981
    ExplanationFactory explanationEngine = ExplanationFactory.CBJ;//NONE suitable for small sets
    //CBJ useful for large variable number, planes=50+
    protected boolean noGoodResults = false;
    public static Solver solver;
    private boolean userInterruption = true;
    String mData;
    String method="RLNS"; //"plns" "elns"
    /**
     * @param data string containing the full trial data, for more information check:
     * http://people.brunel.ac.uk/~mastjjb/jeb/orlib/airlandinfo.html
     */
    public ALP(String data,int r,String method){
        mData=data;
        runways=r;
        this.method=method;
    }
    //DATA
    private int[][] data; //[6+number of planes][number of planes]
    public static int n;

    private static final int ArrivalTime = 0;  //the time a plane appears to the Radar, not used here
    private static final int EearlestTime = 1;  //index in the data array
    private static final int TargetTime = 2; 
    private static final int LatestTime = 3;
    private static final int PenaltyCostBeforeTarget = 4;
    private static final int PenaltyCostAfterTarget = 5;
    private static final int SeparationTime = 6; //index where seperation time exists in the data array.


    public static IntVar[] planes_landing_time,planes_runway, tardiness, earliness; //runways
    BoolVar[] bVars; //binary boolean for airplane conjunction
    int[] costLAT;
    TObjectIntHashMap<IntVar> maxCost;
    int[] LatestTimes;

    public static IntVar objective;

    public void createSolver() {
        solver = new Solver("Aircraft Landing Problem");
    }

    public void buildModel() {
        data = DataFetch.parse(mData);
        n = data.length;
        if(n>44){
            explanationEngine = ExplanationFactory.CBJ; //other options didnt work
        }
        planes_landing_time = new IntVar[n]; //will hold in the end the landing time, should be the optimal(or close to it!)
        planes_runway=new IntVar[n]; //holds run way allocation
        tardiness = new IntVar[n];
        earliness = new IntVar[n];
        LatestTimes = new int[n];
        int objective_upperBound = 0; //objective function upper bound, summation of worse case landing scenario for all planes 
        //within the landing window
        IntVar ZERO = VariableFactory.fixed(0, solver);
        IntVar ONE=VariableFactory.fixed(0, solver);
        for (int i = 0; i < n; i++) {
            planes_landing_time[i] = VariableFactory.bounded("plane_" + i, data[i][EearlestTime], data[i][LatestTime], solver);
            planes_runway[i]=VariableFactory.bounded("plane_r_" + i,1,runways, solver); //one or more runways
            objective_upperBound += Math.max(
                    (data[i][TargetTime] - data[i][EearlestTime]) * data[i][PenaltyCostBeforeTarget],
                    (data[i][LatestTime] - data[i][TargetTime]) * data[i][PenaltyCostAfterTarget]
            );
            earliness[i] = Max.var(ZERO, VariableFactory.offset(VariableFactory.minus(planes_landing_time[i]), data[i][TargetTime]));
            tardiness[i] = Max.var(ZERO, VariableFactory.offset(planes_landing_time[i], -data[i][TargetTime]));
            LatestTimes[i] = data[i][LatestTime];
        }
        List<BoolVar> booleans = new ArrayList<>();
        //disjunctive
        for (int i = 0; i < n - 1; i++) { 
            for (int j = i + 1; j < n; j++) { 
                BoolVar Dij = VariableFactory.bool("b_dij" + i + "_" + j, solver);//Dij =1 if i lands before j
                booleans.add(Dij);
                if(runways==1){   //saving variables in one runway case, but still same principle 
                    Constraint c1 = precedence(planes_landing_time[i], data[i][SeparationTime + j], planes_landing_time[j]);
                    Constraint c2 = precedence(planes_landing_time[j], data[j][SeparationTime + i], planes_landing_time[i]);
                    LogicalConstraintFactory.ifThenElse(Dij, c1,c2);
                }
                else{ //multiple runway
                    BoolVar Zij = VariableFactory.bool("b_zij_" + i + "_" + j, solver); //Zij=1 if i and j land on same runway
                    booleans.add(Zij);
                    
                    //these constraints are applied for airplanes landing on the same runway.
                    Constraint c1 = precedence(planes_landing_time[i], data[i][SeparationTime + j], planes_landing_time[j]);
                    Constraint c2 = precedence(planes_landing_time[j], data[j][SeparationTime + i], planes_landing_time[i]);
                    
                    Constraint c3 = IntConstraintFactory.arithm(planes_runway[i], "=", planes_runway[j]);
                    Constraint c4 = IntConstraintFactory.arithm(planes_runway[i], "!=", planes_runway[j]);
                    //add constraint for both planes on the same run way
                    //planes on same runway are satisfied
                    
                    LogicalConstraintFactory.ifThenElse(Zij,c3,c4);
                    LogicalConstraintFactory.ifThen(LogicalConstraintFactory.and(Dij,Zij), c1); //separation time for
                    //if both are on the same run way, but j follow i then separation time c2 must be satisfied
                    LogicalConstraintFactory.ifThen(LogicalConstraintFactory.and(VariableFactory.not(Dij),Zij), c2);

                    //if i and j are on different runways, then landing time donesnt need to have separation time.
                    Constraint c1_1=IntConstraintFactory.arithm(planes_landing_time[i],"<", planes_landing_time[j]);
                    Constraint c2_1=IntConstraintFactory.arithm(planes_landing_time[j],"<", planes_landing_time[i]);
                    LogicalConstraintFactory.ifThen(LogicalConstraintFactory.and(Dij,VariableFactory.not(Zij)),c1_1);
                    LogicalConstraintFactory.ifThen(LogicalConstraintFactory.and(VariableFactory.not(Dij),VariableFactory.not(Zij)),c2_1);

                }
            }
        }
        
        if(runways>1){
            // runway  decision variable, when a plane is on a runway.
            for (int i = 0; i < n; i++) {
                for (int r = 1; r <= runways; r++) { 
                    BoolVar Yir = VariableFactory.bool("b_Yir_" + i + "_" + r, solver); //if i lands on runway r
                    booleans.add(Yir); 
                    Constraint c1_ir = IntConstraintFactory.arithm(planes_runway[i], "=", r);
                    Constraint c2_ir = IntConstraintFactory.arithm(planes_runway[i], "!=", r);
                    //add constraint for both planes on the same run way
                    LogicalConstraintFactory.ifThenElse(Yir, c1_ir,c2_ir); //else Zero

                    //a plane can only land on one runway Sum yir=1
                }
            }
        }
        bVars = booleans.toArray(new BoolVar[booleans.size()]);

        objective = VariableFactory.bounded("objective", 0, objective_upperBound, solver);

        // build cost array
        costLAT = new int[2 * n];
        maxCost = new TObjectIntHashMap<>();
        for (int i = 0; i < n; i++) {
            costLAT[i] = data[i][PenaltyCostBeforeTarget];
            costLAT[n + i] = data[i][PenaltyCostAfterTarget];
            maxCost.put(planes_landing_time[i], Math.max(data[i][PenaltyCostBeforeTarget], data[i][PenaltyCostAfterTarget]));
        }

//        solver.post(Sum.eq(ArrayUtils.append(earliness, tardiness), costLAT, objective, 1, solver));
        IntVar obj_earliness = VariableFactory.bounded("obj_earliness", 0, objective_upperBound, solver);
        solver.post(IntConstraintFactory.scalar(earliness, Arrays.copyOfRange(costLAT, 0, n), obj_earliness));

        IntVar obj_tardiness = VariableFactory.bounded("obj_tardiness", 0, objective_upperBound, solver);
        solver.post(IntConstraintFactory.scalar(tardiness, Arrays.copyOfRange(costLAT, n, 2 * n), obj_tardiness));
        solver.post(IntConstraintFactory.sum(new IntVar[]{obj_earliness, obj_tardiness}, objective));

        solver.post(IntConstraintFactory.alldifferent(planes_landing_time, "BC"));
     // solver.post(IntConstraintFactory.(planes_runway, "BC"));
        solver.setObjectives(objective);
    }

    static Constraint precedence(IntVar x, int duration, IntVar y) { //duration should become 0 in multiple runways.
        return IntConstraintFactory.arithm(x, "<=", y, "-", duration);
    }

    public void configureSearch() {
        Arrays.sort(planes_landing_time, (o1, o2) -> maxCost.get(o1) - maxCost.get(o2)); //gives better result than the one bellow
        //Arrays.sort(planes_landing_time, (o1, o2) -> maxCost.get(o2) - maxCost.get(o1));
        solver.set(
               IntStrategyFactory.random_bound(bVars, seed),
               IntStrategyFactory.lexico_LB(planes_landing_time)
        );
        StopCriteria.stopSearch=false; //add more stop criterias
        solver.addStopCriterion(new StopCriteria()); //add criteria to stop search by user.
        //solver.makeCompleteSearch(true);
    }

    public void solve() throws Exception{
        IntVar[] ivars = solver.retrieveIntVars();
     //   
        if(method.equals("PLNS")){
            LNSFactory.pglns(solver, ivars, 30, 10, 200, 0, new FailCounter(solver, 100)); //very fast
        }
        else if(method.equals("RLNS")){
            LNSFactory.rlns(solver, ivars, 100/* slower, but better accuracy, 30 acceptable */, seed, new FailCounter(solver, 100)); //level =30 solved all problems
            //except the airland4.txt, with level=100 the problem was solved optimally.
        }
        else if(method.equals("ELNS")){
            LNSFactory.elns(solver, ivars, n, seed, new FailCounter(solver, 100));
        }
        else{
            throw new Exception("Metho must be specified");
        }
      
     //   
        SMF.limitTime(solver, (2*(15+n))+"m"); //PGLNS is not complete. time limit, more runways, more difficult
        //depending on sample size, we limit the fails.   
        solver.findOptimalSolution(ResolutionPolicy.MINIMIZE, objective);
    }

    /*
    called when solution is found and search completes.
    */
    public void printFinalResult() {
        System.out.println(String.format("Air plane landing(%s)", mData));
        StringBuilder st = new StringBuilder();
        if (solver.isFeasible() != ESat.TRUE) {
            st.append("\tINFEASIBLE");
        } else {
            for (int i = 0; i < n; i++) {
                st.append("plane ").append(i).append(" [").
                        append(planes_landing_time[i].getValue()).append(",+").
                        append("]").append(" Runway:"+planes_runway[i].getValue()+"\n");
            }
        }
        System.out.println(st.toString());
        exectuting=false;
    }

 public final boolean readArgs(String... args) {
        CmdLineParser parser = new CmdLineParser(this);
        try {
            parser.parseArgument(args);
        } catch (CmdLineException e) {
            System.err.println(e.getMessage());
            System.err.println("java " + this.getClass() + " [options...]");
            parser.printUsage(System.err);
            System.err.println();
            return false;
        }
        return true;
    }

    protected void overrideExplanation() {
        if (solver.getExplainer() == null) {
            explanationEngine.plugin(solver, noGoodResults, false);
        }
    }
    
    
    private boolean userInterruption() {
        return userInterruption;
    }

    public final void solveProblem(IMonitorSolution mon,String... args) throws Exception {
        this.createSolver();
        this.buildModel();
        this.configureSearch();

        overrideExplanation();

        if (level.getLevel() > SILENT.getLevel()) {
            Chatterbox.showStatistics(solver);
            if (level.getLevel() > Level.VERBOSE.getLevel()) Chatterbox.showSolutions(solver);
            if (level.getLevel() > Level.SOLUTION.getLevel()) Chatterbox.showDecisions(solver);
        }

        Thread statOnKill = new Thread() {
            public void run() {
                if (userInterruption()) {
                    if (level.getLevel() > SILENT.getLevel()) {
                        System.out.println(solver.getMeasures().toString());
                    }
                }

            }
        };

        getRuntime().addShutdownHook(statOnKill);
        solver.plugMonitor(mon);
        this.solve();  //holds tell finish
        if (level.getLevel() > QUIET.getLevel()) {
            printFinalResult();
        }
        userInterruption = false;
        getRuntime().removeShutdownHook(statOnKill);
    }
}