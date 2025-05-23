package nl.tudelft.instrumentation.concolic;

import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

import com.microsoft.z3.*;

import de.learnlib.mapper.api.ContextExecutableInput;

/**
 * You should write your solution using this class.
 * 
 * Z3 API:
 * https://z3prover.github.io/api/html/classcom_1_1microsoft_1_1z3_1_1_context.html
 */
public class ConcolicExecutionLab {

    static Random r = new Random();
    static Boolean isFinished = false;
    static List<String> currentTrace;
    static int traceLength = 10;
    static int noImprove = 0;
    static final int TIME_BUDGET_MS = 5 * 60 * 1000;
    static final int RESTART_THRESHOLD = 15;
    static final int MAX_TRACE_LENGTH = 50;
    static int currentDepth = 0;
    static Set<String> discoveredErrorCodes = new HashSet<>();
    static Set<String> visitedBranches = new HashSet<>();
    static Set<String> satBranches = new HashSet<>();
    static Set<String> unsatBranches = new HashSet<>();
    private static List<BoolExpr> pathConstraints = new ArrayList<>();
    private static PriorityQueue<PrioritizedInput> pendingInputs = new PriorityQueue<>(
            Comparator.<PrioritizedInput>comparingInt(p -> -p.depth));
    private static final int POP_SIZE = 20;
    private static final int GENERATIONS = 05;
    private static final double CROSSOVER_RATE = 0.8;
    private static final double MUTATION_RATE = 0.2;

    static class PrioritizedInput {
        List<String> input;
        int depth;

        PrioritizedInput(List<String> input, int depth) {
            this.input = input;
            this.depth = depth;
        }
    }

    static class Chromosome {
        List<String> trace;
        int fitness;

        Chromosome(List<String> t) {
            this.trace = new ArrayList<>(t);
        }
    }

    static int fitnessOf(List<String> trace) {
        int before = visitedBranches.size();
        PathTracker.reset();
        PathTracker.runNextFuzzedSequence(trace.toArray(new String[0]));
        return visitedBranches.size() - before;

    }

    static List<Chromosome> initialPopulation(String[] syms) {
        List<Chromosome> pop = new ArrayList<>(POP_SIZE);
        pop.add(new Chromosome(currentTrace));
        for (PrioritizedInput pi : pendingInputs) {
            pop.add(new Chromosome(pi.input));
            if (pop.size() >= POP_SIZE) {
                break;
            }

        }
        while (pop.size() < POP_SIZE) {
            pop.add(new Chromosome(generateRandomTrace(syms)));
        }
        return pop;
    }

    static Chromosome crossOver(Chromosome a, Chromosome b) {
        if (r.nextDouble() > CROSSOVER_RATE) {
            return new Chromosome(a.trace);
        }
        int cut = r.nextInt(Math.min(a.trace.size(), b.trace.size()));
        List<String> child = new ArrayList<>();
        child.addAll(a.trace.subList(0, cut));
        child.addAll(b.trace.subList(cut, b.trace.size()));
        return new Chromosome(child);
    }

    static void mutate(Chromosome c, String[] syms) {
        for (int i = 0; i < c.trace.size(); i++) {
            if (r.nextDouble() < MUTATION_RATE) {
                c.trace.set(i, syms[r.nextInt(syms.length)]);
            }
            if (r.nextDouble() < MUTATION_RATE && c.trace.size() > 1) {
                c.trace.remove(r.nextInt(c.trace.size()));
            }
            if (r.nextDouble() < MUTATION_RATE && c.trace.size() < traceLength * 2) {
                c.trace.add(r.nextInt(c.trace.size() + 1), syms[r.nextInt(syms.length)]);
            }
        }
    }

    static void runGA(String[] syms) {
        List<Chromosome> pop = initialPopulation(syms);
        for (int gen = 0; gen < GENERATIONS; gen++) {
            for (Chromosome c : pop) {
                c.fitness = fitnessOf(c.trace);
            }
            pop.sort((x, y) -> Integer.compare(y.fitness, x.fitness));
            List<Chromosome> next = new ArrayList<>(pop.subList(0, POP_SIZE / 2));
            while (next.size() < POP_SIZE) {
                Chromosome p1 = next.get(r.nextInt(next.size()));
                Chromosome p2 = next.get(r.nextInt(next.size()));
                Chromosome child = crossOver(p1, p2);
                mutate(child, syms);
                next.add(child);

            }
            pop = next;
        }
        pop.sort((x, y) -> Integer.compare(y.fitness, x.fitness));
        currentTrace = pop.get(0).trace;

    }

    static void initialize(String[] inputSymbols) {
        // Initialise a random trace from the input symbols of the problem.
        pathConstraints.clear();
        PathTracker.reset();
        visitedBranches.clear();
        pendingInputs.clear();
        satBranches.clear();
        unsatBranches.clear();
        discoveredErrorCodes.clear();
        currentTrace = generateRandomTrace(inputSymbols);

    }

    static int computeFitness(int prevVisitedCount) {
        int now = visitedBranches.size();
        return now - prevVisitedCount;
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
        Expr z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);
        MyVar var = new MyVar(z3var, name);
        PathTracker.inputs.add(var);
        // PathTracker.addToModel(c.mkEq(z3var, value));

        // The following code is to add an additional constraint on the input variable.
        // The input variable must have a value that is equal to one of the input
        // symbols.
        BoolExpr constraint = c.mkFalse();
        for (String input : PathTracker.inputSymbols) {
            constraint = c.mkOr(c.mkEq(z3var, c.mkString(input)), constraint);
        }

        PathTracker.addToModel(constraint);

        return new MyVar(z3var, name);
    }

    static MyVar createBoolExpr(BoolExpr var, String operator) {
        // Handle the following unary operators: !
        Context c = PathTracker.ctx;
        if (!operator.equals("!")) {
            throw new IllegalArgumentException("Unsupported Boolean Operator: " + operator);
        }
        BoolExpr neg = c.mkNot(var);
        return createVar("u_not", neg, c.getBoolSort());
    }

    static MyVar createBoolExpr(BoolExpr left_var, BoolExpr right_var, String operator) {
        // Handle the following binary operators: &, &&, |, ||
        Context c = PathTracker.ctx;
        BoolExpr expr;
        if (operator.equals("&&") || operator.equals("&")) {
            expr = c.mkAnd(left_var, right_var);
        } else if (operator.equals("||") || operator.equals("|")) {
            expr = c.mkOr(left_var, right_var);
        } else {
            throw new IllegalArgumentException("Unsupported Boolean Operator: " + operator);
        }
        return createVar("b_" + operator.replaceAll("\\W", ""), expr, c.getBoolSort());
    }

    static MyVar createIntExpr(IntExpr var, String operator) {
        // Handle the following unary operators for numerical operations: +, -
        if (!operator.equals("+") && !operator.equals("-")) {
            throw new IllegalArgumentException("Unsupported Boolean Operator: " + operator);
        }
        Context c = PathTracker.ctx;
        ArithExpr e = operator.equals("-") ? c.mkUnaryMinus(var) : var;
        return createVar("u_" + operator, e, c.getIntSort());

    }

    static MyVar createIntExpr(IntExpr left_var, IntExpr right_var, String operator) {
        // Handle the following binary operators for numerical operations: +, -, /, *,
        // %, ^, ==, <=, <, >= and >
        Context c = PathTracker.ctx;
        switch (operator) {
            case "+":
                return createVar("i_add", c.mkAdd(left_var, right_var), c.getIntSort());
            case "-":
                return createVar("i_sub", c.mkSub(left_var, right_var), c.getIntSort());
            case "*":
                return createVar("i_mul", c.mkMul(left_var, right_var), c.getIntSort());
            case "/":
                return createVar("i_div", c.mkDiv(left_var, right_var), c.getIntSort());
            case "%":
                return createVar("i_mod", c.mkMod(left_var, right_var), c.getIntSort());
            case "^":
                return createVar("i_pow", c.mkPower(left_var, right_var), c.getIntSort());
            case "==":
                return createVar("i_eq", c.mkEq(left_var, right_var), c.getBoolSort());
            case "<=":
                return createVar("i_le", c.mkLe(left_var, right_var), c.getBoolSort());
            case "<":
                return createVar("i_lt", c.mkLt(left_var, right_var), c.getBoolSort());
            case ">=":
                return createVar("i_ge", c.mkGe(left_var, right_var), c.getBoolSort());
            case ">":
                return createVar("i_add", c.mkGt(left_var, right_var), c.getBoolSort());
            default:
                throw new IllegalArgumentException("Unsupported Operator Arithmetic: " + operator);
        }
    }

    static MyVar createStringExpr(SeqExpr left_var, SeqExpr right_var, String operator) {
        // We only support String.equals
        Context c = PathTracker.ctx;
        if (!operator.equals("equals") && !operator.equals("==")) {
            throw new IllegalArgumentException("Unsupported String Operator: " + operator);
        }
        BoolExpr eq = c.mkEq(left_var, right_var);
        return createVar("s_eq", eq, c.getBoolSort());
    }

    static void assign(MyVar var, String name, Expr value, Sort s) {
        // All variable assignments, use single static assignment
        Context c = PathTracker.ctx;
        Expr z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);
        PathTracker.addToModel(c.mkEq(z3var, value));
        var.z3var = z3var;
        var.name = name;
    }

    static void encounteredNewBranch(MyVar condition, boolean value, int line_nr) {
        String takenKey = line_nr + ":" + value;
        String flipKey = line_nr + ":" + !value;
        if (visitedBranches.contains(takenKey)) {
            return;
        }
        visitedBranches.add(takenKey);
        System.out.println("Taken Key: " + takenKey);
        // Call the solver
        Context ct = PathTracker.ctx;
        // Solver solver = PathTracker.solver;

        BoolExpr actualCondition = (BoolExpr) condition.z3var;
        BoolExpr taken = value ? actualCondition : ct.mkNot(actualCondition);
        currentDepth++;

        // pathConstraints.add(taken);
        // solver.add(taken);
        // PathTracker.addToModel(taken);
        // PathTracker.addToBranches(taken);

        BoolExpr flipped = ct.mkNot(taken);
        if (!satBranches.contains(flipKey) && !unsatBranches.contains(flipKey)) {
            PathTracker.solve(flipped, false);
            System.out.println("Inputs: " + PathTracker.inputs);
            Status st = PathTracker.solver.check();
            if (st == Status.SATISFIABLE) {
                System.out.println("Found Satisfiable value");
                satBranches.add(flipKey);
                // Model model = solver.getModel();
                // LinkedList<String> modelInputs = new LinkedList<>();
                // for (MyVar v : PathTracker.inputs) {
                // Expr valueExpr = model.eval(v.z3var, true);
                // if (valueExpr != null && valueExpr.isString()) {
                // modelInputs.add(valueExpr.toString());
                // }

                // }
                // System.out.println("New Inputs: " + modelInputs);
                // newSatisfiableInput(modelInputs);

            } else {
                System.out.println("Unsat branch found: " + flipKey);
                unsatBranches.add(flipKey);
            }
            System.out.println("Pending Inputs size: " + pendingInputs.size());
        }

    }

    static void newSatisfiableInput(LinkedList<String> new_inputs) {
        // Hurray! found a new branch using these new inputs!
        // Remove the extra quotes from the inputs that were find by the solver.
        List<String> trimmed_new_inputs = new_inputs.stream()
                .map(s -> s.replaceAll("\"", ""))
                .collect(Collectors.toList());
        int depth = currentDepth;
        System.out.println("Current Depth: " + depth);
        pendingInputs.add(new PrioritizedInput(trimmed_new_inputs, depth));
        System.out.println("Pending Inputs size: " + pendingInputs.size());
        noImprove = 0;
        System.out.println("** New branch found! Queued input of depth " + depth + ": " + trimmed_new_inputs);

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
        if (!pendingInputs.isEmpty()) {

            List<String> nextSolverInput = pendingInputs.poll().input;
            System.out.println("Fuzz() using solver-derived input: " + nextSolverInput);
            return nextSolverInput;
        }
        noImprove++;
        if (noImprove >= RESTART_THRESHOLD) {
            noImprove = 0;
            System.out.println("★ Random restart ★");
            return generateRandomTrace(inputSymbols);
        }
        System.out.println("No solver inputs left, doing a GA burst…");
        runGA(inputSymbols);
        return currentTrace;
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
        long startTime = System.currentTimeMillis();
        long endTime = startTime + TIME_BUDGET_MS;
        int traceCount = 0;
        PathTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));
        traceCount++;
        System.out.println("Executed initial trace of length " + currentTrace.size());

        // Place here your code to guide your fuzzer with its search using Concolic
        // Execution.
        // while (!isFinished) {
        // // Do things!
        // try {
        // System.out.println("Woohoo, looping!");
        // Thread.sleep(1000);
        // } catch (InterruptedException e) {
        // e.printStackTrace();
        // }
        // }
        while (System.currentTimeMillis() < endTime) {
            PathTracker.reset();
            pathConstraints.clear();
            currentDepth = 0;
            List<String> inputs = fuzz(PathTracker.inputSymbols);
            currentTrace = inputs;
            PathTracker.runNextFuzzedSequence(inputs.toArray(new String[0]));
            traceCount++;
            // System.out.println("Executed trace of length " + inputs.size());

        }
        System.out.println("==== Experiment finished (5 min) ====");
        System.out.println("Total traces executed: " + traceCount);
        System.out.println("Branches visited: " + visitedBranches.size());
        System.out.println("Pending inputs remaining: " + pendingInputs.size());
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