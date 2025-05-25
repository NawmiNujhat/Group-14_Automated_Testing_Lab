package nl.tudelft.instrumentation.concolic;

import java.io.FileWriter;
import java.io.IOException;
import java.time.Duration;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import com.microsoft.z3.*;

import nl.tudelft.instrumentation.fuzzing.DistanceTracker;

/**
 * You should write your solution using this class.
 * 
 * Z3 API:
 * https://z3prover.github.io/api/html/classcom_1_1microsoft_1_1z3_1_1_context.html
 */
public class ConcolicExecutionLab {

    static Random r = new Random();
    static List<String> currentTrace;
    static int traceLength = 10;
    static int currentDepth = 0;
    static int branchCount = 0;
    static int noImprove = 0;
    static Set<String> discoveredErrorCodes = new HashSet<>();
    static Set<String> visitedBranches = new HashSet<>();
    static Set<String> pathConstraints = new HashSet<>();
    static Set<String> satBranches = new HashSet<>();
    static Set<String> unsatBranches = new HashSet<>();
    private static PriorityQueue<PrioritizedInput> pendingInputs = new PriorityQueue<>((a, b) -> {
        int d = Integer.compare(b.depth, a.depth);
        if (d != 0)
            return d;
        return Double.compare(a.distance, b.distance);
    });
    static final double RESTART_PROBABILITY = 0.05;
    static final int TIME_BUDGET_MS = 5 * 60 * 1000;
    static final int RESTART_THRESHOLD = 20;
    static final int MAX_TRACE_LENGTH = 200;
    static double distance = 0.0;
    private static final Map<Expr, CondInfo> condInfo = new HashMap<>();

    private static class PrioritizedInput {
        List<String> input;
        int depth;
        double distance;

        PrioritizedInput(List<String> input, int depth, double distance) {
            this.input = input;
            this.depth = depth;
            this.distance = distance;
        }
    }

    private enum Kind {
        BOOL, INT, STRING
    };

    private static class CondInfo {
        final Kind kind;
        final String op;
        final MyVar left, right;

        CondInfo(Kind kind, String op, MyVar left, MyVar right) {
            this.kind = kind;
            this.op = op;
            this.left = left;
            this.right = right;
        }
    }

    static void initialize(String[] inputSymbols) {
        // Initialise a random trace from the input symbols of the problem.
        visitedBranches.clear();
        unsatBranches.clear();
        satBranches.clear();
        pendingInputs.clear();
        branchCount = 0;
        currentTrace = generateRandomTrace(inputSymbols);
    }

    static MyVar createVar(String name, Expr value, Sort s) {
        Context c = PathTracker.ctx;
        /**
         * Create var, assign value and add to path constraint.
         * We show how to do it for creating new symbols, please
         * add similar steps to the functions below in order to
         * obtain a path constraint.
         */
        Expr z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);
        PathTracker.addToModel(c.mkEq(z3var, value));
        return new MyVar(z3var, name);
    }

    static MyVar createInput(String name, Expr value, Sort s) {
        // Create an input var, these should be free variables!
        Context c = PathTracker.ctx;

        Expr z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s); // creating z3var, from createVar
                                                                                     // function above
        MyVar inputVariable = new MyVar(z3var);

        // The following code is to add an additional constraint on the input variable.
        // The input variable must have a value that is equal to one of the input
        // symbols.
        BoolExpr constraint = c.mkFalse();
        for (String input : PathTracker.inputSymbols) {
            constraint = c.mkOr(c.mkEq(z3var, c.mkString(input)), constraint);
        }

        PathTracker.addToModel(constraint);
        PathTracker.inputs.add(inputVariable);
        // TODO: check if input needs to be stored anywhere
        return inputVariable;
    }

    static MyVar createBoolExpr(BoolExpr var, String operator) {
        // Handle the following unary operators: !
        MyVar v = new MyVar(PathTracker.ctx.mkNot(var));
        condInfo.put(v.z3var, new CondInfo(Kind.BOOL, "!", new MyVar(var, ""), null));
        return v;
    }

    static MyVar createBoolExpr(BoolExpr left_var, BoolExpr right_var, String operator) {
        // Handle the following binary operators: &, &&, |, ||
        MyVar v = null;
        switch (operator) {
            case "&":
            case "&&":
                v = new MyVar(PathTracker.ctx.mkAnd(left_var, right_var));
                break;
            case "|":
            case "||":
                v = new MyVar(PathTracker.ctx.mkOr(left_var, right_var));
                break;
            default:
                System.out.println("Unknow Operator in Bool: " + operator);
                System.exit(0);
                v = new MyVar(PathTracker.ctx.mkFalse());
                break;
        }
        condInfo.put(v.z3var,
                new CondInfo(Kind.BOOL, operator,
                        new MyVar(left_var, /* dummy */""),
                        new MyVar(right_var, /* dummy */"")));
        return v;

    }

    static MyVar createIntExpr(IntExpr var, String operator) {
        // Handle the following unary operators for numerical operations: +, -

        // '+' just stays the same number, only handle '-'
        MyVar v = null;
        if (operator.equals("-"))
            v = new MyVar(PathTracker.ctx.mkSub(PathTracker.ctx.mkInt(0), var));
        condInfo.put(v.z3var, new CondInfo(Kind.INT, operator, new MyVar(var, ""), null));
        return v;
    }

    static MyVar createIntExpr(IntExpr left_var, IntExpr right_var, String operator) {
        // Handle the following binary operators for numerical operations: +, -, /, *,
        // %, ^, ==, <=, <, >= and >
        MyVar v = null;
        switch (operator) {
            case "+":
                v = new MyVar(PathTracker.ctx.mkAdd(left_var, right_var));
                condInfo.put(v.z3var,
                        new CondInfo(Kind.INT, operator, new MyVar(left_var, ""), new MyVar(right_var, "")));
                return v;

            case "-":
                v = new MyVar(PathTracker.ctx.mkSub(left_var, right_var));
                condInfo.put(v.z3var,
                        new CondInfo(Kind.INT, operator, new MyVar(left_var, ""), new MyVar(right_var, "")));
                return v;
            case "/":
                v = new MyVar(PathTracker.ctx.mkDiv(left_var, right_var));
                condInfo.put(v.z3var,
                        new CondInfo(Kind.INT, operator, new MyVar(left_var, ""), new MyVar(right_var, "")));
                return v;
            case "*":
                v = new MyVar(PathTracker.ctx.mkMul(left_var, right_var));
                condInfo.put(v.z3var,
                        new CondInfo(Kind.INT, operator, new MyVar(left_var, ""), new MyVar(right_var, "")));
                return v;
            case "%":
                v = new MyVar(PathTracker.ctx.mkMod(left_var, right_var));
                condInfo.put(v.z3var,
                        new CondInfo(Kind.INT, operator, new MyVar(left_var, ""), new MyVar(right_var, "")));
                return v;
            case "^":
                v = new MyVar(PathTracker.ctx.mkPower(left_var, right_var));
                condInfo.put(v.z3var,
                        new CondInfo(Kind.INT, operator, new MyVar(left_var, ""), new MyVar(right_var, "")));
                return v;
            case "==":
                v = new MyVar(PathTracker.ctx.mkEq(left_var, right_var));
                condInfo.put(v.z3var,
                        new CondInfo(Kind.INT, operator, new MyVar(left_var, ""), new MyVar(right_var, "")));
                return v;
            case "<=":
                v = new MyVar(PathTracker.ctx.mkLe(left_var, right_var));
                condInfo.put(v.z3var,
                        new CondInfo(Kind.INT, operator, new MyVar(left_var, ""), new MyVar(right_var, "")));
                return v;
            case "<":
                v = new MyVar(PathTracker.ctx.mkLt(left_var, right_var));
                condInfo.put(v.z3var,
                        new CondInfo(Kind.INT, operator, new MyVar(left_var, ""), new MyVar(right_var, "")));
                return v;
            case ">=":
                v = new MyVar(PathTracker.ctx.mkGe(left_var, right_var));
                condInfo.put(v.z3var,
                        new CondInfo(Kind.INT, operator, new MyVar(left_var, ""), new MyVar(right_var, "")));
                return v;
            case ">":
                v = new MyVar(PathTracker.ctx.mkGt(left_var, right_var));
                condInfo.put(v.z3var,
                        new CondInfo(Kind.INT, operator, new MyVar(left_var, ""), new MyVar(right_var, "")));
                return v;
            default:
                System.out.println("Unknow Operator in IntExpres: " + operator);
                System.exit(0);
                v = new MyVar(PathTracker.ctx.mkFalse());
                return v;
        }

    }

    static MyVar createStringExpr(SeqExpr left_var, SeqExpr right_var, String operator) {
        // We only support String.equals
        MyVar v = null;
        if (operator.equals("==")) {
            v = new MyVar(PathTracker.ctx.mkEq(left_var, right_var));
            condInfo.put(
                    v.z3var,
                    new CondInfo(
                            Kind.STRING,
                            operator,
                            new MyVar(left_var, ""),
                            new MyVar(right_var, "")));
            return v;
        }
        System.out.println("Unknow Operator in StringExprs: " + operator);
        System.exit(0);
        return null;
    }

    static void assign(MyVar var, String name, Expr value, Sort s) {
        // All variable assignments, use single static assignment
        Context c = PathTracker.ctx;
        // Set MyVar's z3var in same way as createVar function
        var.z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);
        PathTracker.addToModel(c.mkEq(var.z3var, value));
    }

    static double rawBranchDistance(MyVar condition, boolean actualValue) {

        CondInfo info = condInfo.get(condition.z3var);
        if (info == null) {
            return actualValue ? 0.0 : 1.0;
        }

        double raw;
        switch (info.kind) {
            case BOOL:
                switch (info.op) {
                    case "!":
                        // unary negation: distance is zero if actualValue matches !operand
                        boolean operand = Boolean.parseBoolean(info.left.z3var.getSExpr());
                        raw = (actualValue == (!operand)) ? 0.0 : 1.0;
                        break;
                    case "&&":
                    case "&":
                        // to satisfy A && B, both must be true
                        if (actualValue) {
                            double d1 = rawBranchDistance(info.left, true);
                            double d2 = rawBranchDistance(info.right, true);
                            raw = d1 + d2;
                        } else {
                            // if the conjunction failed, pick the smaller distance to flipping either side
                            double d1f = rawBranchDistance(info.left, false);
                            double d2f = rawBranchDistance(info.right, false);
                            raw = Math.min(d1f, d2f);
                        }
                        break;
                    case "||":
                    case "|":
                        // to satisfy A || B, at least one must be true
                        if (actualValue) {
                            // if it succeeded, pick the smaller distance to making either side true
                            double d1 = rawBranchDistance(info.left, true);
                            double d2 = rawBranchDistance(info.right, true);
                            raw = Math.min(d1, d2);
                        } else {
                            // if the disjunction failed (both false), sum their distances
                            raw = rawBranchDistance(info.left, false)
                                    + rawBranchDistance(info.right, false);
                        }
                        break;
                    default:
                        // fall back to simple boolean mismatch
                        raw = actualValue ? 0.0 : 1.0;
                }
                break;

            case INT: {
                long l = Long.parseLong(info.left.z3var.getSExpr());
                long r = Long.parseLong(info.right.z3var.getSExpr());
                switch (info.op) {
                    case "==":
                        raw = actualValue ? 0.0 : Math.abs(l - r);
                        break;
                    case "!=":
                        raw = actualValue ? 0.0 : (l == r ? 1.0 : 0.0);
                        break;
                    case "<":
                        raw = actualValue ? 0.0 : Math.max(0, l - r + 1);
                        break;
                    case "<=":
                        raw = actualValue ? 0.0 : Math.max(0, l - r);
                        break;
                    case ">":
                        raw = actualValue ? 0.0 : Math.max(0, r - l + 1);
                        break;
                    case ">=":
                        raw = actualValue ? 0.0 : Math.max(0, r - l);
                        break;
                    default:
                        raw = 1.0;
                }
            }
                break;

            case STRING: {
                String ls = info.left.z3var.toString().replaceAll("^\"|\"$", "");
                String rs = info.right.z3var.toString().replaceAll("^\"|\"$", "");
                if (info.op.equals("equals") || info.op.equals("==")) {
                    raw = actualValue ? 0.0 : editDistance(ls, rs);
                } else {
                    raw = 1.0;
                }
            }
                break;

            default:
                raw = actualValue ? 0.0 : 1.0;
        }

        // normalize into [0,1)
        return raw / (raw + 1.0);
    }

    static int editDistance(String str1, String str2) {
        int m = str1.length();
        int n = str2.length();
        int[][] dp = new int[m + 1][n + 1];
        for (int i = 0; i <= m; i++) {
            for (int j = 0; j <= n; j++) {
                if (i == 0) {
                    dp[i][j] = j;
                } else if (j == 0) {
                    dp[i][j] = i;
                } else if (str1.charAt(i - 1) == str2.charAt(j - 1)) {
                    dp[i][j] = dp[i - 1][j - 1];
                } else {
                    dp[i][j] = 1 + Math.min(
                            Math.min(dp[i][j - 1],
                                    dp[i - 1][j]),
                            dp[i - 1][j - 1]);
                }
            }
        }
        return dp[m][n];
    }

    static void encounteredNewBranch(MyVar condition, boolean value, int line_nr) {

        Context c = PathTracker.ctx;
        String takenKey = line_nr + ":" + value;
        String flipKey = line_nr + ":" + !value;
        visitedBranches.add(takenKey);
        satBranches.remove(takenKey);
        BoolExpr currentValue = value ? c.mkTrue() : c.mkFalse();
        // System.out.println("Actual Condition Value: "+currentValue.getSExpr());
        if (!satBranches.contains(flipKey) && !visitedBranches.contains(flipKey)) {
            BoolExpr flippedCondition = value ? c.mkFalse() : c.mkTrue();
            // System.out.println("Flipped Condition Value: " +
            // flippedCondition.getSExpr());
            PathTracker.solver.push();
            PathTracker.solver.add(flippedCondition);
            // Step 3: Try to find a satisfying model
            if (PathTracker.solver.check() == Status.SATISFIABLE) {
                System.out.println("Found Satisfiable: ");
                Model model = PathTracker.solver.getModel();
                LinkedList<String> newInputs = new LinkedList<>();
                for (MyVar inputVar : PathTracker.inputs) {
                    newInputs.add(model.evaluate(inputVar.z3var, true).toString());
                }
                satBranches.add(flipKey);
                distance = rawBranchDistance(condition, !value);
                ConcolicExecutionLab.newSatisfiableInput(newInputs);
            } else {
                System.out.println("Unsatisfiable Value Found!");
                unsatBranches.add(flipKey);
            }
            PathTracker.solver.pop();

        }
        PathTracker.addToBranches(c.mkEq(condition.z3var, currentValue));
        currentDepth++;
    }

    static void newSatisfiableInput(LinkedList<String> new_inputs) {
        // Hurray! found a new branch using these new inputs!
        // Remove the extra quotes from the inputs that were find by the solver.
        // System.out.println("Found new satisfiable input.");
        List<String> trimmed_new_inputs = new_inputs.stream()
                .map(s -> s.replaceAll("\"", ""))
                .collect(Collectors.toList());

        System.out.println("Trimmed new inputs: " + trimmed_new_inputs);

        pendingInputs.add(new PrioritizedInput(trimmed_new_inputs, currentDepth, distance));
        // System.out.println("Input trace queue size: " + pendingInputs.size());
        // noImprove = 0; TODO: check this
        branchCount++;
    }

    /**
     * Method for fuzzing new inputs for a program.
     * 
     * @param inputSymbols the inputSymbols to fuzz from.
     * @return a fuzzed sequence
     */
    static List<String> fuzz(String[] inputSymbols) {
        /*
         * Add here your code for fuzzing a new sequence for the RERS problem.
         * You can guide your fuzzer to fuzz "smart" input sequences to cover
         * more branches using concolic execution. Right now we just generate
         * a complete random sequence using the given input symbols. Please
         * change it to your own code.
         */
        return generateRandomTrace(inputSymbols);
    }

    /**
     * Generate a random trace from an array of symbols.
     * 
     * @param symbols the symbols from which a trace should be generated from.
     * @return a random trace that is generated from the given symbols.
     */
    static List<String> generateRandomTrace(String[] symbols) {
        ArrayList<String> trace = new ArrayList<>();
        for (int i = 0; i < traceLength; i++) {
            trace.add(symbols[r.nextInt(symbols.length)]);
        }
        return trace;
    }

    static List<String> padCurrentTrace(List<String> new_trace) {
        int missing = traceLength - new_trace.size();
        Random rnd = new Random();
        return Stream
                .concat(
                        new_trace.stream(),
                        Stream.generate(() -> PathTracker.inputSymbols[rnd.nextInt(PathTracker.inputSymbols.length)])
                                .limit(missing))
                .collect(Collectors.toCollection(ArrayList::new));
    }

    static void run() {
        initialize(PathTracker.inputSymbols);
        long startTime = System.currentTimeMillis();
        long deadline = startTime + TIME_BUDGET_MS;
        double epsilon = 0.25;
        double decay = 0.9995;
        double epsilon_min = 0.05;
        int lastBranchCount=0;

        // Place here your code to guide your fuzzer with its search using Concolic
        // Execution.
        while (System.currentTimeMillis() < deadline) {
            currentDepth = 0;
            if (branchCount > lastBranchCount) { 
                epsilon = Math.max(epsilon_min, epsilon * decay);
                lastBranchCount = branchCount;
            } else {
                epsilon = Math.min(1.0, epsilon + 0.05);
            }
            boolean explore = Math.random() < epsilon && pendingInputs.isEmpty();

            try {
                if (explore) {
                    currentTrace = generateRandomTrace(PathTracker.inputSymbols);
                    noImprove++;
                    PathTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));

                } else {
                    List<String> nextSolverInput = pendingInputs.poll().input;
                    System.out.println("Input: " + nextSolverInput);
                    currentTrace = nextSolverInput;
                    noImprove = 0;
                    PathTracker.runNextFuzzedSequence(padCurrentTrace(currentTrace).toArray(new String[0]));

                }
                
                if (noImprove >= RESTART_THRESHOLD) {
                    noImprove = 0;
                    epsilon = 1.0;
                    traceLength = Math.min(MAX_TRACE_LENGTH, traceLength + 5);
                    currentTrace = generateRandomTrace(PathTracker.inputSymbols);
                    PathTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));
                    System.out.println("→ random restart (new length = " + traceLength + ")");
                }
                if (epsilon > epsilon_min) {
                    epsilon = Math.max(epsilon_min, epsilon * decay);
                }
                PathTracker.reset();

            } catch (Exception e) {
                e.printStackTrace();
            }

            System.out.println("trace length: " + traceLength);
            System.out.println("Input trace queue size: " + pendingInputs.size());
            System.out.println("Current known branches: " + branchCount);
            System.out.println("Visited Branches: " + visitedBranches.size());
            PathTracker.reset();
            // satBranches.clear();
            // unsatBranches.clear();
            // pendingInputs.clear();
        }

        System.out.println("Run completed.");

        // Finished, write results to csv
        exportResultsToCSV();
    }

    public static void output(String out) {
        // System.out.println(out);
        if (out.contains("error_") || out.contains("Error")) {
            String error_code = out.replaceFirst("^Invalid input:\\s*", "");
            discoveredErrorCodes.add(error_code.trim());
        }
    }

    static void exportResultsToCSV() {
        String fileName = "concolic_results.csv";
        boolean fileExists = new java.io.File(fileName).exists();
        try (FileWriter writer = new FileWriter(fileName, true)) {
            if (!fileExists) {
                writer.write("# of Unique Branches, # of Unique Error Codes, Error Codes\n");
            }

            // Avoid comma issues
            String errorCodesJoined = discoveredErrorCodes.stream()
                    .map(code -> code.replaceAll(".*?(\\d+)", "$1")) // Extract numeric part
                    .sorted(Comparator.comparingInt(Integer::parseInt))
                    .collect(Collectors.joining("|"));

            writer.write(visitedBranches.size() + ","
                    + discoveredErrorCodes.size() + ","
                    + errorCodesJoined + "\n");

            System.out.println("Results written to " + fileName);
        } catch (IOException e) {
            System.err.println("Failed to write results to CSV: " + e.getMessage());
        }
    }

}