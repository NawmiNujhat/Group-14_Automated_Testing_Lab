package nl.tudelft.instrumentation.fuzzing;

import java.util.*;
import java.util.stream.Collectors;
import java.io.FileWriter;
import java.io.IOException;

/**
 * You should write your own solution using this class.
 */
public class FuzzingLab {
        static Random r = new Random();
        static List<String> currentTrace;
        static int traceLength = 10;
        static boolean isFinished = false;
        static boolean sawInvalid = false;
        static Map<Integer, Double> latestBranchDistances = new HashMap<>();
        static Set<Integer> visitedBranches = new HashSet<>();
        static Set<String> discoveredErrorCodes = new HashSet<>();
        static Set<Integer> localBranches = new HashSet<>();
        static final int MUTATIONS_PER_ITERATION = 20;
        static final int TIME_BUDGET_MS = 5 * 60 * 1000;
        static final double RESTART_PROBABILITY = 0.1;
        static final double K = 0.1;
        static final boolean RANDOM = true; // Update when switching fuzzing method

        static void initialize(String[] inputSymbols) {
                // Initialise a random trace from the input symbols of the problem.
                currentTrace = generateRandomTrace(inputSymbols);
        }

        /**
         * Write your solution that specifies what should happen when a new branch has
         * been found.
         */
        static void encounteredNewBranch(MyVar condition, boolean value, int line_nr) {
                double raw = rawBranchDistance(condition, value);
                // System.out.println("Raw Branch Distance: "+raw);
                double normalizedDistance = normalize(raw);
                if (!localBranches.contains(line_nr)) {
                        localBranches.add(line_nr);
                        visitedBranches.add(line_nr);
                }
                latestBranchDistances.put(line_nr, normalizedDistance);
                // if (normalizedDistance > 0.0) {
                // System.out.println("Branch at line " + line_nr + ": " + condition.toString()
                // +
                // " evaluated as " + value + " with distance " + normalizedDistance);
                // }
                // System.out.println(condition.toString());
        }

        static double normalize(double distance) {

                return distance / (distance + 1.0);
        }

        static double rawBranchDistance(MyVar condition, boolean actualValue) {
                switch (condition.type) {
                        case UNKNOWN:
                                return 1.0;
                        case BOOL:

                                if (condition.value == actualValue) {
                                        return 0.0;
                                } else {
                                        return 1.0;
                                }
                        case INT:
                        case STRING:
                                return 1.0;
                        case BINARY:
                                switch (condition.operator) {
                                        case "==":
                                                if (condition.left.type == TypeEnum.STRING
                                                                && condition.right.type == TypeEnum.STRING) {
                                                        String leftStr = condition.left.str_value;
                                                        String rightStr = condition.right.str_value;
                                                        return actualValue ? 0 : editDistance(leftStr, rightStr);
                                                } else {
                                                        double leftval = condition.left.int_value;
                                                        double rightval = condition.right.int_value;
                                                        return actualValue ? 0.0 : Math.abs(leftval - rightval);
                                                }
                                        case "!=":
                                                if (condition.left.type == TypeEnum.STRING
                                                                && condition.right.type == TypeEnum.STRING) {
                                                        String leftStr = condition.left.str_value;
                                                        String rightStr = condition.right.str_value;
                                                        return actualValue ? 0 : (leftStr.equals(rightStr) ? 1 : 0);
                                                } else {
                                                        double leftval = condition.left.int_value;
                                                        double rightval = condition.right.int_value;
                                                        double diff = Math.abs(leftval - rightval);
                                                        return actualValue ? 0 : ((diff == 0) ? 1 : 0);
                                                }
                                        case "<":
                                                double leftval = condition.left.int_value;
                                                double rightval = condition.right.int_value;
                                                return actualValue ? 0 : Math.max(0, leftval - rightval + 1);
                                        case "<=":
                                                leftval = condition.left.int_value;
                                                rightval = condition.right.int_value;
                                                return actualValue ? 0 : Math.max(0, leftval - rightval);
                                        case ">":
                                                leftval = condition.left.int_value;
                                                rightval = condition.right.int_value;
                                                return actualValue ? 0 : Math.max(0, rightval - leftval + 1);
                                        case ">=":
                                                leftval = condition.left.int_value;
                                                rightval = condition.right.int_value;
                                                return actualValue ? 0 : Math.max(0, rightval - leftval);

                                        case "&&":
                                        case "&":
                                                if (actualValue) {
                                                        return 0.0;
                                                } else {
                                                        double leftdist = rawBranchDistance(condition.left,
                                                                        actualValue);
                                                        double rightdist = rawBranchDistance(condition.right,
                                                                        actualValue);
                                                        return leftdist + rightdist;

                                                }
                                        case "||":
                                        case "|":
                                                if (actualValue) {
                                                        return 0.0;
                                                } else {
                                                        double leftdist = rawBranchDistance(condition.left,
                                                                        actualValue);
                                                        double rightdist = rawBranchDistance(condition.right,
                                                                        actualValue);
                                                        return Math.min(leftdist, rightdist);

                                                }
                                        case "^":
                                        case "XOR":
                                                if (actualValue) {
                                                        return 0.0;
                                                } else {
                                                        double d1 = rawBranchDistance(condition.left, actualValue) +
                                                                        rawBranchDistance(condition.right,
                                                                                        !actualValue);
                                                        double d2 = rawBranchDistance(condition.right, actualValue) + (1
                                                                        - rawBranchDistance(condition.left,
                                                                                        !actualValue));
                                                        return Math.min(d1, d2);

                                                }

                                        default:
                                                return actualValue ? 0.0 : 1.0;

                                }
                        case UNARY:
                                if (condition.operator.equals("!")) {
                                        return actualValue ? 0 : (1 - rawBranchDistance(condition.left, !actualValue));
                                }
                                return 1.0;
                        default:
                                return actualValue ? 0 : 1;
                }

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

        /**
         * Method for fuzzing new inputs for a program.
         * 
         * @param inputSymbols the inputSymbols to fuzz from.
         * @return a fuzzed sequence
         */
        static double calculateFitness(List<String> trace) {
                latestBranchDistances.clear();
                localBranches.clear();
                sawInvalid = false;
                // discoveredErrorCodes.clear();
                try {
                        DistanceTracker.runNextFuzzedSequence(trace.toArray(new String[0]));
                } catch (SecurityException se) {
                        sawInvalid = true;
                } catch (IllegalStateException ise) {
                        discoveredErrorCodes.add(ise.getMessage()); 
                        // System.out.println(ise.getMessage());
                        return Double.POSITIVE_INFINITY; 
                } catch (Throwable t) {
                        t.printStackTrace();
                }
                if (sawInvalid) {
                        return Double.POSITIVE_INFINITY;
                }
                double fitness = latestBranchDistances.values().stream().mapToDouble(d -> d).sum();
                return fitness;
        }

        static List<String> mutateTrace(List<String> trace, String[] inputSymbols) {
                List<String> mutated = new ArrayList<>(trace);
                int mutationType = r.nextInt(4);
                switch (mutationType) {
                        case 0:
                                if (mutated.size() > 0) {
                                        int index = r.nextInt(mutated.size());
                                        mutated.set(index, inputSymbols[r.nextInt(inputSymbols.length)]);
                                }
                                break;
                        case 1:
                                mutated.add(inputSymbols[r.nextInt(inputSymbols.length)]);
                                break;
                        case 2:
                                if (mutated.size() > 1) {
                                        int index = r.nextInt(mutated.size());
                                        mutated.remove(index);
                                }
                                break;
                        case 3:
                                if (mutated.size() > 1) {
                                        int index1 = r.nextInt(mutated.size());
                                        int index2 = r.nextInt(mutated.size());
                                        while (index2 == index1) {
                                                index2 = r.nextInt(mutated.size());
                                        }
                                        String temp = mutated.get(index1);
                                        mutated.set(index1, mutated.get(index2));
                                        mutated.set(index2, temp);

                                }
                                break;

                }
                if (mutated.isEmpty()) {
                        mutated.add(inputSymbols[r.nextInt(inputSymbols.length)]);
                }
                return mutated;

        }

        static List<String> hillClimbing(String[] inputSymbols) {
                // List<String> bestTrace = new ArrayList<>(currentTrace);
                // double bestFitness = calculateFitness(bestTrace);
                // System.out.println("Best Trace Obtained: " + bestTrace);
                List<String> bestTrace = null;
                double bestFitness = Double.POSITIVE_INFINITY;
                final int MAX_TRIES = 20;
                for (int t = 0; t < MAX_TRIES; t++) {
                        List<String> cand = generateRandomTrace(inputSymbols);
                        double fit = calculateFitness(cand);
                        if (!Double.isInfinite(fit)) {
                                bestTrace = cand;
                                bestFitness = fit;
                                break;
                        }
                }
                if (bestTrace == null) {
                        String good = inputSymbols[0];
                        for (String s : inputSymbols) {
                                if (!Double.isInfinite(calculateFitness(Collections.singletonList(s)))) {
                                        good = s;
                                        break;
                                }
                        }
                        bestTrace = new ArrayList<>();
                        for (int i = 0; i < traceLength; i++) {
                                bestTrace.add(good);
                        }
                        bestFitness = calculateFitness(bestTrace);
                }
                System.out.println("Bootstrap seed (f=" + bestFitness + "): " + bestTrace);

                boolean improved = false;
                for (int i = 0; i < MUTATIONS_PER_ITERATION; i++) {
                        System.out.println("Mutating Trace");
                        List<String> mutatedTrace = mutateTrace(bestTrace, inputSymbols);
                        System.out.println("Input Symbols: "+ inputSymbols);
                        System.out.println("Mutated Trace" + mutatedTrace);
                        double mutatedFitness = calculateFitness(mutatedTrace);
                        System.out.println("Mutated Fitness: " + mutatedFitness);
                        System.out.println("Best Fitness: " + bestFitness);
                        if (Double.isInfinite(mutatedFitness)) {
                                continue;
                        }
                        if (mutatedFitness < bestFitness) {
                                bestTrace = mutatedTrace;
                                bestFitness = mutatedFitness;
                                System.out.println("Found Better trace with Fitness: " + bestFitness + ", branches: "
                                                + visitedBranches.size());
                                improved = true;
                        }
                }
                if (!improved) {
                        System.out.println("Bestfitness not obtained");
                        bestTrace = generateRandomTrace(inputSymbols);
                }
                return bestTrace;

        }

        static List<String> fuzz(String[] inputSymbols) {
                /*
                 * Add here your code for fuzzing a new sequence for the RERS problem.
                 * You can guide your fuzzer to fuzz "smart" input sequences to cover
                 * more branches. Right now we just generate a complete random sequence
                 * using the given input symbols. Please change it to your own code.
                 */
                if (RANDOM) {
                        return generateRandomTrace(inputSymbols);
                }

                // Hill climbing implementation
                
                if (r.nextDouble() < RESTART_PROBABILITY) {
                        return generateRandomTrace(inputSymbols);
                }
                return hillClimbing(inputSymbols);
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
                initialize(DistanceTracker.inputSymbols);
                // Place here your code to guide your fuzzer with its search.
                int noImprovementCounter = 0;
                int previousBranchCount = 0;
                long deadline = System.currentTimeMillis() + TIME_BUDGET_MS;
                List<String> bestTrace = null;
                System.out.println("Starting fuzzing with hill climbing...");
                while (System.currentTimeMillis() < deadline) {
                        System.out.printf("Time left: %d ms\n", (deadline - System.currentTimeMillis()));

                        // DistanceTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));

                        try {
                                currentTrace = fuzz(DistanceTracker.inputSymbols);
                                DistanceTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));
                        } catch (SecurityException se) {
                                discoveredErrorCodes.add(se.getMessage());
                                // System.out.println(se.getMessage());
                        } catch (IllegalStateException ise) {
                                discoveredErrorCodes.add(ise.getMessage());
                                // System.out.println(ise.getMessage());
                        } catch (Throwable t) {
                                t.printStackTrace();
                        }

                        System.out.printf("Covered %d branches, found %d error codes\n",
                                        visitedBranches.size(), discoveredErrorCodes.size());
                        previousBranchCount = visitedBranches.size();
                        if (visitedBranches.size() <= previousBranchCount) {
                                noImprovementCounter++;
                        } else {
                                bestTrace = currentTrace;
                        }
                        System.out.printf("No Improvement found in %d cases", noImprovementCounter);
                }
                System.out.printf("Time's up! Unique branches: %d, error codes: %d\n",
                                visitedBranches.size(), discoveredErrorCodes.size());
                System.out.println("Error codes: " + discoveredErrorCodes);

                // Write results to csv
                exportResultsToCSV(bestTrace);
        }

        /**
         * Method that is used for catching the output from standard out.
         * You should write your own logic here.
         * 
         * @param out the string that has been outputted in the standard out.
         */
        public static void output(String out) {
                // System.out.println(out);
                // if (out.startsWith("Invalid input:")) {
                // discoveredErrorCodes.add(out);
                // return;
                // }
                
                if (out.contains("error_") || out.contains("Error")) {
                        String error_code = out.replaceFirst("^Invalid input:\\s*", "");
                        System.out.println("Added Error Code: " + error_code);
                        discoveredErrorCodes.add(error_code.trim());
                }
        }


        static void exportResultsToCSV(List<String> bestTrace) {
                String fileName = "fuzzing_results.csv";
                boolean fileExists = new java.io.File(fileName).exists();
                try (FileWriter writer = new FileWriter(fileName, true)) {
                        if (!fileExists) {
                                writer.write("# of Unique Branches, # of Unique Error Codes, Error Codes, Best Trace\n");
                        }

                        // Avoid comma issues
                        String errorCodesJoined = discoveredErrorCodes.stream()
                                .map(code -> code.replaceAll(",", ";").trim()) 
                                .collect(Collectors.joining("|"));
                        
                        writer.write(visitedBranches.size() + ","
                                + discoveredErrorCodes.size() + ","
                                + errorCodesJoined + ","
                                + bestTrace + "\n");

                        System.out.println("Results written to " + fileName);
                } catch (IOException e) {
                        System.err.println("Failed to write results to CSV: " + e.getMessage());
                }
        }

}
