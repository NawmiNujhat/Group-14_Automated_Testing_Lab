package nl.tudelft.instrumentation.concolic;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.time.Duration;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
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
    static long startTime = System.currentTimeMillis();
    static int traceLength = 10;
    static int currentDepth = 0;
    static int branchCount = 0;
    static int noImprove = 0;
    static Set<String> discoveredErrorCodes = new HashSet<>();
    static Set<String> visitedBranches = new HashSet<>();
    static Set<String> pathConstraints = new HashSet<>();
    static Set<String> satBranches = new HashSet<>();
    static Set<String> unsatBranches = new HashSet<>();
    private static PriorityQueue<PrioritizedInput> pendingInputs = new PriorityQueue<>();
    static final int TIME_BUDGET_MS = 5 * 60 * 1000;
    static final int RESTART_THRESHOLD = 10;
    static Set<String> errorCodeOutput = new HashSet<>();
    static final int MAX_TRACE_LENGTH = 200;
    static double distance = 0.0;

    private static class PrioritizedInput implements Comparable<PrioritizedInput> {
        List<String> input;
        int depth;

        PrioritizedInput(List<String> input, int depth) {
            this.input = input;
            this.depth = depth;
        }

        @Override
        public int compareTo(PrioritizedInput other) {
            return Integer.compare(this.depth, other.depth);
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
        return v;
    }

    static MyVar createBoolExpr(BoolExpr left_var, BoolExpr right_var, String operator) {
        // Handle the following binary operators: &, &&, |, ||
        MyVar v = null;
        switch (operator) {
            case "&":
            case "&&":
                return new MyVar(PathTracker.ctx.mkAnd(left_var, right_var));

            case "|":
            case "||":
                return new MyVar(PathTracker.ctx.mkOr(left_var, right_var));
            default:
                System.out.println("Unknow Operator in Bool: " + operator);
                System.exit(0);
                return new MyVar(PathTracker.ctx.mkFalse());

        }

    }

    static MyVar createIntExpr(IntExpr var, String operator) {
        // Handle the following unary operators for numerical operations: +, -

        // '+' just stays the same number, only handle '-'
        MyVar v = null;
        if (operator.equals("-"))
            return new MyVar(PathTracker.ctx.mkSub(PathTracker.ctx.mkInt(0), var));
        return new MyVar(var);

    }

    static MyVar createIntExpr(IntExpr left_var, IntExpr right_var, String operator) {
        // Handle the following binary operators for numerical operations: +, -, /, *,
        // %, ^, ==, <=, <, >= and >
        MyVar v = null;
        switch (operator) {
            case "+":
                return new MyVar(PathTracker.ctx.mkAdd(left_var, right_var));

            case "-":
                return new MyVar(PathTracker.ctx.mkSub(left_var, right_var));

            case "/":
                return new MyVar(PathTracker.ctx.mkDiv(left_var, right_var));

            case "*":
                return new MyVar(PathTracker.ctx.mkMul(left_var, right_var));

            case "%":
                return new MyVar(PathTracker.ctx.mkMod(left_var, right_var));

            case "^":
                return new MyVar(PathTracker.ctx.mkPower(left_var, right_var));

            case "==":
                return new MyVar(PathTracker.ctx.mkEq(left_var, right_var));

            case "<=":
                return new MyVar(PathTracker.ctx.mkLe(left_var, right_var));

            case "<":
                return new MyVar(PathTracker.ctx.mkLt(left_var, right_var));

            case ">=":
                return new MyVar(PathTracker.ctx.mkGe(left_var, right_var));

            case ">":
                return new MyVar(PathTracker.ctx.mkGt(left_var, right_var));

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
            return new MyVar(PathTracker.ctx.mkEq(left_var, right_var));
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

    static void encounteredNewBranch(MyVar condition, boolean value, int line_nr) {

        Context c = PathTracker.ctx;
        String takenKey = line_nr + ":" + value;
        String flipKey = line_nr + ":" + !value;
        visitedBranches.add(takenKey);
        satBranches.remove(takenKey);
        BoolExpr currentValue = value ? c.mkTrue() : c.mkFalse();
        BoolExpr flipped = value ? c.mkFalse() : c.mkTrue();
        if (!satBranches.contains(flipKey) && !visitedBranches.contains(flipKey)) {
            BoolExpr flippedCondition = c.mkEq(condition.z3var, flipped);
            PathTracker.solver.push();
            PathTracker.solver.add(flippedCondition);
            // Step 3: Try to find a satisfying model
            if (PathTracker.solver.check() == Status.SATISFIABLE) {
                // System.out.println("Found Satisfiable: ");
                Model model = PathTracker.solver.getModel();
                LinkedList<String> newInputs = new LinkedList<>();
                for (MyVar inputVar : PathTracker.inputs) {
                    newInputs.add(model.evaluate(inputVar.z3var, true).toString());
                }
                satBranches.add(flipKey);
                ConcolicExecutionLab.newSatisfiableInput(newInputs);
            } else {
                // System.out.println("Unsatisfiable Value Found!");
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

        pendingInputs.add(new PrioritizedInput(trimmed_new_inputs, currentDepth));
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

    static List<String> padCurrentTrace(List<String> newTrace) {
        int missing = traceLength - newTrace.size();
        Random rnd = new Random();
        IntStream.range(0, missing)
                .mapToObj(i -> PathTracker.inputSymbols[rnd.nextInt(PathTracker.inputSymbols.length)])
                .forEach(newTrace::add);
        return newTrace;
    }

    static double computeRestartProbability(long t) {
        // Time-based decay 
        double initialTimeProb = 0.9;
        double minTimeProb = 0.2;
        double decayConstant = 60.0; 

        return minTimeProb + (initialTimeProb - minTimeProb) * Math.exp(-t / decayConstant);
    }
    static void run() {
        initialize(PathTracker.inputSymbols);
        long startTime = System.currentTimeMillis();
        long deadline = startTime + TIME_BUDGET_MS;
        double restartProb = 0.0;
        // Place here your code to guide your fuzzer with its search using Concolic
        // Execution.
        while (System.currentTimeMillis() < deadline) {
            currentDepth = 0;
            restartProb = computeRestartProbability(startTime);
            try {
                if (Math.random() >= restartProb) {
                    if (!pendingInputs.isEmpty()) {
                        List<String> nextSolverInput = pendingInputs.poll().input;
                        System.out.println("Input: " + nextSolverInput);
                        currentTrace = nextSolverInput;
                        noImprove = 0;
                        PathTracker.runNextFuzzedSequence(padCurrentTrace(currentTrace).toArray(new String[0]));

                    } else {
                        noImprove++;
                        if (noImprove >= RESTART_THRESHOLD) {
                            noImprove = 0;
                            traceLength += 5;

                        }
                        currentTrace = generateRandomTrace(PathTracker.inputSymbols);
                        PathTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));
                        System.out.println("→ random restart (new length = " + traceLength + ")");

                    }

                } else {

                    currentTrace = generateRandomTrace(PathTracker.inputSymbols);
                    PathTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));
                }

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
            long currentTimeElapsed = (System.currentTimeMillis() - startTime) / 1000;
            if (!discoveredErrorCodes.contains(error_code)) {
                errorCodeOutput.add(error_code.trim() + "(" + currentTimeElapsed + "s)");
            }
            discoveredErrorCodes.add(error_code.trim());
        }
    }

    static void exportResultsToCSV() {
        String fileName = "concolic_results.csv";
        String errorFileName = "concolic_errors.csv";
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
        try (BufferedWriter writer = new BufferedWriter(new FileWriter(errorFileName, true))) {
            if (!fileExists) {
                writer.write("Error Codes\n");
            }

            writer.write(errorCodeOutput.stream().collect(Collectors.joining("|")));
            writer.newLine();

            System.out.println("Results written to " + errorFileName);
        } catch (IOException e) {
            System.err.println("Failed to write results to CSV: " + e.getMessage());
        }
    }

}