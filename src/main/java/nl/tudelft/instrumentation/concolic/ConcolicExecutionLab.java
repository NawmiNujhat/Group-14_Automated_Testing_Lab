package nl.tudelft.instrumentation.concolic;

import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

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
    static Queue<Node> input_trace_queue = new LinkedList<Node>();
    static Set<String> pathConstraints = new HashSet<>();
    static Set<String> satBranches = new HashSet<>();
    static Set<String> unsatBranches = new HashSet<>();

    static final int TIME_BUDGET_MS = 5 * 60 * 1000;
    static final int RESTART_THRESHOLD = 15;
    static final int MAX_TRACE_LENGTH = 50;

    static class Node {
        List<String> element;

        Node(List<String> el) {
            this.element = el;
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
        pathConstraints.remove(takenKey);
        if (satBranches.contains(flipKey) || visitedBranches.contains(flipKey)) {
            return;
        }

        // Call the solver
        Context c = PathTracker.ctx;
        // Negate the current condition
        BoolExpr currentValue = value ? c.mkTrue() : c.mkFalse();
        BoolExpr flippedCondition = c.mkNot(currentValue);

        PathTracker.solver.push();
        PathTracker.solver.add(flippedCondition);

        // Step 3: Try to find a satisfying model
        if ( PathTracker.solver.check() == Status.SATISFIABLE) {
            System.out.println("Found Satisfiable: ");
            Model model =  PathTracker.solver.getModel();
            LinkedList<String> newInputs = new LinkedList<>();
            for (MyVar inputVar : PathTracker.inputs) {
                newInputs.add(model.evaluate(inputVar.z3var, true).toString());
            }
            satBranches.add(flipKey);
            ConcolicExecutionLab.newSatisfiableInput(newInputs);
        }
        else{
            System.out.println("Unsatidfiable Value Found!");
            unsatBranches.add(flipKey);
        }

        currentDepth++;
        PathTracker.solver.pop();
        PathTracker.addToBranches(c.mkEq(condition.z3var,currentValue));
    }

    static void newSatisfiableInput(LinkedList<String> new_inputs) {
        // Hurray! found a new branch using these new inputs!
        // Remove the extra quotes from the inputs that were find by the solver.
        // System.out.println("Found new satisfiable input.");
        List<String> trimmed_new_inputs = new_inputs.stream()
                .map(s -> s.replaceAll("\"", ""))
                .collect(Collectors.toList());

        // TODO: Check if currentDepth needs to be stored along side for priority?? BFS
        // right?
        input_trace_queue.add(new Node(trimmed_new_inputs));
        System.out.println("Input trace queue size: " + input_trace_queue.size());
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

    static void run() {
        initialize(PathTracker.inputSymbols);
        long deadline = System.currentTimeMillis() + TIME_BUDGET_MS;

        // Place here your code to guide your fuzzer with its search using Concolic
        // Execution.
        while (System.currentTimeMillis() < deadline) {
            currentDepth = 0;

            try {
                if (!input_trace_queue.isEmpty()) {
                    Node el = input_trace_queue.poll();

                    System.out.println("Element: " + el.element);
                    currentTrace = el.element;
                    PathTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));
                } else {
                    noImprove++;
                    if (noImprove >= RESTART_THRESHOLD) {
                        noImprove = 0;
                        traceLength = Math.min(MAX_TRACE_LENGTH, traceLength + 1);

                        // Restart from random trace
                        currentTrace = generateRandomTrace(PathTracker.inputSymbols);
                    }
                    PathTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));
                }
            } catch (Exception e) {
                e.printStackTrace();
            }
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
                    + errorCodesJoined);

            System.out.println("Results written to " + fileName);
        } catch (IOException e) {
            System.err.println("Failed to write results to CSV: " + e.getMessage());
        }
    }

}