package nl.tudelft.instrumentation.fuzzing;

import java.util.*;
import java.util.concurrent.CancellationException;
import java.util.concurrent.TimeoutException;
import java.util.stream.Collectors;
import java.io.FileWriter;
import java.io.IOException;

/**
 * You should write your own solution using this class.
 */
public class FuzzingLab {
        static Random r = new Random();
        static List<String> currentTrace;
        static double temperature = 5.0;
        static final double COOL_RATE = 0.98;
        static double currentFitness = Double.POSITIVE_INFINITY;
        static int traceLength = 20;
        static int maxTraceLength = 50;
        static boolean isFinished = false;
        static boolean sawInvalid = false;
        static Map<Integer, Double> latestBranchDistances = new HashMap<>();
        static Set<Integer> visitedBranches = new HashSet<>();
        static Set<String> discoveredErrorCodes = new HashSet<>();
        static List<Integer> lastExecutionPath = new ArrayList<>();
        static int targetBranchLine = -1;
        static final int MAX_BRANCHES_PER_RUN = 10_000;
        static int branchCount;
        static double sumBranchDistance = 0.0;

        static final int MUTATIONS_PER_ITERATION = 20;
        static final int RESTART_THRESHOLD = MUTATIONS_PER_ITERATION;
        static final int TIME_BUDGET_MS = 5 * 60 * 1000;
        static final double RESTART_PROBABILITY = 0.05;
        static final double K = 0.1; // Update when switching fuzzing method
        static final boolean RANDOM = true; // Update when switching fuzzing method
        static Set<Integer> allBranches = new HashSet<>();
        static int noImprove = 0;
        static boolean recordCoverage = true;
        static Set<Integer> currentTraceCoverage = null;

        static void initialize(String[] inputSymbols) {
                // Initialise a random trace from the input symbols of the problem.
                currentTrace = generateRandomTrace(inputSymbols);
        }

        /**
         * Write your solution that specifies what should happen when a new branch has
         * been found.
         */
        static int edgeId(int line, boolean outcome) {
                return (line << 1) | (outcome ? 1 : 0);
        }

        static void encounteredNewBranch(MyVar condition, boolean value, int line_nr) {
                // if (++branchCount > MAX_BRANCHES_PER_RUN) {
                // throw new SecurityException(
                // "Exceeded " + MAX_BRANCHES_PER_RUN + " branches in one run");
                // }

                double raw = rawBranchDistance(condition, !value);
                double normalizedDistance = normalize(raw);
                sumBranchDistance += normalizedDistance;

                int idToken = edgeId(line_nr, !value); // edge we just took
                int other = edgeId(line_nr, value);
                visitedBranches.add(idToken);

                latestBranchDistances.put(idToken, normalizedDistance);
                latestBranchDistances.putIfAbsent(other, 1 - normalizedDistance);
                lastExecutionPath.add(idToken);
                allBranches.add(other);
                allBranches.add(edgeId(line_nr, !value));

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
                                                return actualValue ? 0 : Math.max(0, leftval - rightval + K);
                                        case "<=":
                                                leftval = condition.left.int_value;
                                                rightval = condition.right.int_value;
                                                return actualValue ? 0 : Math.max(0, leftval - rightval);
                                        case ">":
                                                leftval = condition.left.int_value;
                                                rightval = condition.right.int_value;
                                                return actualValue ? 0 : Math.max(0, rightval - leftval + K);
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
                lastExecutionPath.clear();
                sawInvalid = false;

                try {
                        DistanceTracker.runNextFuzzedSequence(trace.toArray(new String[0]));
                } catch (SecurityException | CancellationException te) {
                        sawInvalid = true;
                } catch (IllegalStateException ise) {
                        discoveredErrorCodes.add(ise.getMessage());
                } catch (Throwable t) {
                        if (t instanceof TimeoutException) {
                                return Double.POSITIVE_INFINITY;
                        } else {
                                t.printStackTrace();
                        }
                }

                if (sawInvalid) {
                        return Double.POSITIVE_INFINITY;
                }
                // double branchDistance;
                // if (targetBranchLine == -1) {
                // branchDistance = 0.0;
                // }
                // else if (latestBranchDistances.containsKey(targetBranchLine)) {
                // branchDistance = latestBranchDistances.get(targetBranchLine);
                // } else if (!lastExecutionPath.isEmpty()) {
                // int diverging = lastExecutionPath.get(lastExecutionPath.size() - 1);
                // branchDistance = latestBranchDistances.getOrDefault(diverging, 1.0);
                // } else {
                // branchDistance = 1.0;
                // }
                // double branchDistance = 1.0;
                // if (targetBranchLine != -1) {
                // branchDistance = latestBranchDistances.getOrDefault(targetBranchLine, 1.0);
                // }
                // double branchDistance = 0.0;
                // for (int edge : allBranches) {
                // if (!visitedBranches.contains(edge)) {
                // // if we've seen a distance for that edge, use it, else 1.0
                // branchDistance += latestBranchDistances.getOrDefault(edge, 1.0);
                // }
                // }
                // System.out.println("Branch Distance: " + branchDistance);
                double branchDistance = allBranches.stream()
                                .filter(e -> !visitedBranches.contains(e))
                                .mapToDouble(e -> latestBranchDistances.getOrDefault(e, 1.0))
                                .sum();
                int approachLevel = computeApproachLevel();
                if (RANDOM) {
                        return branchDistance;
                }
                // System.out.println("Approach Level: " + approachLevel);
                return branchDistance + approachLevel;
        }

        static int computeApproachLevel() {
                if (targetBranchLine == -1 || lastExecutionPath.isEmpty())
                        return 0;
                int index = 0;
                for (int line : lastExecutionPath) {
                        if (line == targetBranchLine)
                                return 0;
                        index++;
                }
                return index;
        }

        static List<String> mutateTrace(List<String> trace) {
                List<String> mutated = new ArrayList<>(trace);
                int mutationType = r.nextInt(7);
                String[] symbols = DistanceTracker.inputSymbols;
                switch (mutationType) {
                        case 0:
                                int idx = r.nextInt(mutated.size());
                                if (mutated.size() > 0) {
                                        int index = r.nextInt(mutated.size());
                                        mutated.set(idx,
                                                        DistanceTracker.inputSymbols[r
                                                                        .nextInt(DistanceTracker.inputSymbols.length)]);
                                }
                                break;
                        case 1:
                                mutated.add(DistanceTracker.inputSymbols[r
                                                .nextInt(DistanceTracker.inputSymbols.length)]);
                                break;
                        case 2:
                                if (mutated.size() > 1) {
                                        mutated.remove(r.nextInt(mutated.size()));
                                }
                                break;
                        case 3:
                                if (mutated.size() > 1) {
                                        int i = r.nextInt(mutated.size()), j = r.nextInt(mutated.size());
                                        Collections.swap(mutated, i, j);
                                }
                                break;
                        case 4: // brand-new mutation
                                int pos = r.nextInt(mutated.size() + 1);
                                String sym = DistanceTracker.inputSymbols[r.nextInt(symbols.length)];
                                mutated.add(pos, sym);
                                break;
                        case 5: // delete‐and‐insert
                                if (mutated.size() > 0)
                                        mutated.remove(r.nextInt(mutated.size()));
                                mutated.add(r.nextInt(mutated.size() + 1), symbols[r.nextInt(symbols.length)]);
                                break;
                        case 6: // shrink‐and‐grow
                                if (!mutated.isEmpty())
                                        mutated.remove(r.nextInt(mutated.size()));
                                if (mutated.size() < maxTraceLength)
                                        mutated.add(r.nextInt(mutated.size() + 1), symbols[r.nextInt(symbols.length)]);
                                break;

                }
                if (mutated.isEmpty()) {
                        mutated.add(mutated.get(r.nextInt(symbols.length)));
                        mutated.add(mutated.get(r.nextInt(symbols.length)));
                }
                return mutated;

        }

        static List<String> hillClimbing(String[] inputSymbols) {
                List<String> bestTrace = new ArrayList<>(currentTrace);
                double bestFitness = calculateFitness(bestTrace);
                for (int i = 0; i < MUTATIONS_PER_ITERATION; i++) {
                        List<String> mutatedTrace = mutateTrace(bestTrace);
                        double mutatedFitness = calculateFitness(mutatedTrace);
                        boolean accept = (mutatedFitness <= bestFitness);
                        if (!accept) {
                                double delta = bestFitness - mutatedFitness; // positive if cand is worse
                                double p = Math.exp(delta / temperature);
                                if (r.nextDouble() < p) {
                                        accept = true;
                                }
                        }
                        if (accept) {
                                bestTrace = mutatedTrace;
                                bestFitness = mutatedFitness;
                        }
                }
                temperature = Math.max(0.01, temperature * COOL_RATE);
                return bestTrace;

        }

        static List<String> fuzz(String[] inputSymbols) {
                /*
                 * Add here your code for fuzzing a new sequence for the RERS problem.
                 * You can guide your fuzzer to fuzz "smart" input sequences to cover
                 * more branches. Right now we just generate a complete random sequence
                 * using the given input symbols. Please change it to your own code.
                 */
                if (RANDOM || r.nextDouble() < RESTART_PROBABILITY) {
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
                int bestCov = 0;
                long deadline = System.currentTimeMillis() + TIME_BUDGET_MS;
                List<String> bestTrace = null;
                double cur=Double.POSITIVE_INFINITY;
                double fitness = 0.0;
                if (RANDOM) {
                        // only one random trace, then exit
                        while (System.currentTimeMillis() < deadline) {
                                visitedBranches.clear();
                                initialize(DistanceTracker.inputSymbols);
                                currentTrace = fuzz(DistanceTracker.inputSymbols);
                                try {
                                        fitness=calculateFitness(currentTrace);
                                } catch (CancellationException e) {
                                        continue;
                                } catch (SecurityException | IllegalStateException e) {
                                        continue;
                                } catch (Throwable t) {
                                        if (t instanceof java.util.concurrent.TimeoutException) {
                                                continue;
                                        }
                                        throw t;
                                }
                                int cov = visitedBranches.size();
                                if (cov > bestCov && fitness<=cur) {
                                        bestCov = cov;
                                        bestTrace = new ArrayList<>(currentTrace);
                                }
                                System.out.printf("Random only covered %d branches\n", visitedBranches.size());
                        }
                        exportResultsToCSV(bestTrace);
                        return;

                }
                initialize(DistanceTracker.inputSymbols);
                while (System.currentTimeMillis() < deadline) {
                        if (targetBranchLine == -1 || visitedBranches.contains(targetBranchLine)) {
                                targetBranchLine = allBranches.stream()
                                                .filter(id -> !visitedBranches.contains(id))
                                                .min(Comparator.comparingDouble(
                                                                e -> latestBranchDistances.getOrDefault(e, 1.0)))
                                                .orElse(-1);

                        }

                        currentTrace = fuzz(DistanceTracker.inputSymbols);
                        fitness = calculateFitness(currentTrace);
                        if (fitness <= currentFitness) {
                                currentFitness = fitness;
                                bestTrace = currentTrace;
                                noImprove = 0;
                        } else {
                                noImprove++;
                                // if we went a full batch with no gain, restart from scratch
                                if (noImprove >= RESTART_THRESHOLD) {
                                        noImprove = 0;
                                        currentTrace = generateRandomTrace(DistanceTracker.inputSymbols);
                                        currentFitness = calculateFitness(currentTrace);
                                        traceLength = Math.min(maxTraceLength, traceLength + 1);
                                        temperature = 1.0;
                                }
                        }
                        System.out.printf("Covered %d branches, fitness %.2f\n", visitedBranches.size(),
                                        currentFitness);
                }
                exportResultsToCSV(bestTrace);
        }

        /**
         * Method that is used for catching the output from standard out.
         * You should write your own logic here.
         * 
         * @param out the string that has been outputted in the standard out.
         */
        public static void output(String out) {
                if (out.contains("error_") || out.contains("Error")) {
                        String error_code = out.replaceFirst("^Invalid input:\\s*", "");
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
                                        .map(code -> code.replaceAll(".*?(\\d+)", "$1")) // Extract numeric part
                                        .sorted(Comparator.comparingInt(Integer::parseInt))
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