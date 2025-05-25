package nl.tudelft.instrumentation.concolic;

import java.io.FileWriter;
import java.io.IOException;
import java.time.Duration;
import java.time.Instant;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.Map.Entry;
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
    static Instant start = Instant.now();
    static List<String> currentTrace;
    static int traceLength = 10;
    static int currentDepth = 0;
    static int branchCount = 0;
    static int noImprove = 0;
    static Boolean isFinished = false;
    static Set<String> discoveredErrorCodes = new HashSet<>();
    static Set<String> visitedBranches = new HashSet<>();
    static Set<String> satBranches = new HashSet<>();
    static Set<String> unsatBranches = new HashSet<>();
    static Set<Entry<Boolean, Integer>> known_branches = new HashSet<>();
    static Set<Entry<Boolean, Integer>> will_solve_branches = new HashSet<>();
    private static PriorityQueue<PrioritizedInput> pendingInputs = new PriorityQueue<>(Comparator.<PrioritizedInput>comparingInt(p -> -p.depth));

    static final int TIME_BUDGET_MS = 5 * 60 * 1000;
    static final int RESTART_THRESHOLD = 10;
    static final int MAX_TRACE_LENGTH = 100;

    static class PrioritizedInput {
        List<String> input;
        int depth;

        PrioritizedInput(List<String> input, int depth) {
            this.input = input;
            this.depth = depth;
        }
    }

    static void initialize(String[] inputSymbols) {
        // Initialise a random trace from the input symbols of the problem.
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
        PathTracker.inputs.add(inputVariable);
        // The following code is to add an additional constraint on the input variable.
        // The input variable must have a value that is equal to one of the input
        // symbols.
        BoolExpr constraint = c.mkFalse();
        for (String input : PathTracker.inputSymbols) {
            constraint = c.mkOr(c.mkEq(z3var, c.mkString(input)), constraint);
        }

        PathTracker.addToModel(constraint);
        // TODO: check if input needs to be stored anywhere
        return inputVariable;
    }

    static MyVar createBoolExpr(BoolExpr var, String operator) {
        // Handle the following unary operators: !
        return new MyVar(PathTracker.ctx.mkNot(var));
    }

    static MyVar createBoolExpr(BoolExpr left_var, BoolExpr right_var, String operator) {
        // Handle the following binary operators: &, &&, |, ||
        switch (operator) {
            case "&":
            case "&&":
                return new MyVar(PathTracker.ctx.mkAnd(left_var, right_var));
            case "|":
            case "||":
                return new MyVar(PathTracker.ctx.mkOr(left_var, right_var));
            default:
                throw new IllegalArgumentException("Unknown operator: " + operator);
        }
    }

    static MyVar createIntExpr(IntExpr var, String operator) {
        // Handle the following unary operators for numerical operations: +, -

        // '+' just stays the same number, only handle '-'
        if (operator.equals("-"))
            return new MyVar(PathTracker.ctx.mkSub(PathTracker.ctx.mkInt(0), var));
        return new MyVar(var);
    }

    static MyVar createIntExpr(IntExpr left_var, IntExpr right_var, String operator) {
        // Handle the following binary operators for numerical operations: +, -, /, *,
        // %, ^, ==, <=, <, >= and >
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
                throw new IllegalArgumentException("Unknown operator: " + operator);
        }
    }

    static MyVar createStringExpr(SeqExpr left_var, SeqExpr right_var, String operator) {
        // We only support String.equals
        if (operator.equals("==")) {
            return new MyVar(PathTracker.ctx.mkEq(left_var, right_var));
        }
        throw new IllegalArgumentException("Unknown operator: " + operator);
    }

    static void assign(MyVar var, String name, Expr value, Sort s) {
        // All variable assignments, use single static assignment
        Context c = PathTracker.ctx;
        // Set MyVar's z3var in same way as createVar function
        var.z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);
        PathTracker.addToModel(c.mkEq(var.z3var, value));
    }

    static void encounteredNewBranch(MyVar condition, boolean value, int line_nr) {
        String takenKey = line_nr + ":" + value;
        String flipKey = line_nr + ":" + !value;
        visitedBranches.add(takenKey);
        satBranches.remove(takenKey);

        // Call the solver
        Context c = PathTracker.ctx;

        // Negate the current condition
        BoolExpr currentValue = value ? c.mkTrue() : c.mkFalse();
        BoolExpr flippedCondition = value ? c.mkFalse() : c.mkTrue();

        if (!satBranches.contains(flipKey) && !visitedBranches.contains(flipKey)) {
            PathTracker.solver.push();
            PathTracker.solver.add(c.mkEq(condition.z3var, flippedCondition));

            // Step 3: Try to find a satisfying model
            if (PathTracker.solver.check() == Status.SATISFIABLE) {
                System.out.println("Found Satisfiable: ");
                satBranches.add(flipKey);
                Model model =  PathTracker.solver.getModel();
                LinkedList<String> newInputs = new LinkedList<>();
                for (MyVar inputVar : PathTracker.inputs) {
                    newInputs.add(model.evaluate(inputVar.z3var, true).toString());
                }
                ConcolicExecutionLab.newSatisfiableInput(newInputs);
            }
            else{
                // System.out.println("Unsatidfiable Value Found!");
                unsatBranches.add(flipKey);
            }

            PathTracker.solver.pop();
        }

        currentDepth++;
        PathTracker.addToBranches(c.mkEq(condition.z3var, currentValue));
    }

    static void newSatisfiableInput(LinkedList<String> new_inputs) {
        // Hurray! found a new branch using these new inputs!
        // Remove the extra quotes from the inputs that were find by the solver.
        // System.out.println("Found new satisfiable input.");
        List<String> trimmed_new_inputs = new_inputs.stream()
                .map(s -> s.replaceAll("\"", ""))
                .collect(Collectors.toList());

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

    /**
     * Computes a restart probability based on time progress.
     *
     * @param t                Time elapsed since the start of the run (in seconds)
     * @return                 Restart probability (between 0.05 and 0.9)
     */
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
        long deadline = System.currentTimeMillis() + TIME_BUDGET_MS;

        while (System.currentTimeMillis() <= deadline) {
            currentDepth = 0;
            double restartProbability = computeRestartProbability(startTime);

            try {
                if (r.nextDouble() < restartProbability) {
                    if (!pendingInputs.isEmpty()) {
                        List<String> nextSolverInput = pendingInputs.poll().input;
                        List<String> fullLengthTrace = Stream.concat(
                            nextSolverInput.stream(),
                            Stream.generate(() -> PathTracker.inputSymbols[r.nextInt(PathTracker.inputSymbols.length)])
                                .limit(traceLength - nextSolverInput.size())
                        ).collect(Collectors.toList());
                        System.out.println("Trace: " + fullLengthTrace);
                        PathTracker.runNextFuzzedSequence(fullLengthTrace.toArray(new String[0]));
                    } else {
                        noImprove++;
                        if(noImprove >= RESTART_THRESHOLD) {
                            noImprove = 0;
                            traceLength = Math.min(MAX_TRACE_LENGTH, traceLength + 5);
                        }
                        PathTracker.runNextFuzzedSequence(generateRandomTrace(PathTracker.inputSymbols).toArray(new String[0]));
                    }
                } else {
                    PathTracker.runNextFuzzedSequence(generateRandomTrace(PathTracker.inputSymbols).toArray(new String[0]));
                }
            }
            catch(Exception e) {
                e.printStackTrace();
            }

            System.out.println("Input trace length: " + traceLength);
            System.out.println("Pending inputs size: " + pendingInputs.size());
            System.out.println("Visited branches: " + visitedBranches.size());
            PathTracker.reset();
        }

        // Finished, write to csv
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