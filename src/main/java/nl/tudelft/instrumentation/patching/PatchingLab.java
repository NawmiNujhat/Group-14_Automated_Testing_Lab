package nl.tudelft.instrumentation.patching;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.*;

public class PatchingLab {

        static Random r = new Random();
        static boolean isFinished = false;
        static int numOperators;
        static double[] tarantulaScore;
        static String[] originalOperators;
        private static final String BEST_FIT_FILE = "best_fitness.txt";
        static int numField;
        static boolean[] execBitMap;
        private static int[] passCount;
        private static int[] failCount;
        private static int totalPass, totalFail;
        private static final Random RNG = new Random();
        private static final int POP_SIZE = 20;
        private static final int MAX_GEN = 500;
        private static final double BASE_MUT_P = 0.05;
        private static final int TOP_SUSPECTS = 5;
        private static final String[] NUMERIC_OPS = { ">", "<", ">=", "<=", "==", "!=" };
        private static final String[] BOOLEAN_OPS = { "==", "!=" };

        static final List<Integer> fitnessHistory = new ArrayList<>();

        static void initialize() {
                // initialize the population based on OperatorTracker.operators
                originalOperators = OperatorTracker.operators.clone();
                numOperators = originalOperators.length;
                passCount = new int[numOperators];
                failCount = new int[numOperators];
                execBitMap = new boolean[numOperators];
                tarantulaScore = new double[numOperators];

        }

        static int computeFitness(List<Boolean> resuList) {
                numField = 0;
                for (boolean passed : resuList) {
                        if (!passed) {
                                numField++;
                        }
                }
                return numField;

        }

        static int runAndCollect() {
                Arrays.fill(passCount, 0);
                Arrays.fill(failCount, 0);
                totalPass = totalFail = 0;
                int nTests = OperatorTracker.runAllTests().size();
                int failing = 0;
                for (int i = 0; i < nTests; i++) {
                        // System.out.println("Number of tests: " + nTests);
                        Arrays.fill(execBitMap, false);
                        boolean passed = OperatorTracker.runTest(i);
                        if (passed)
                                totalPass++;
                        else {
                                totalFail++;
                                failing++;
                        }
                        for (int j = 0; j < numOperators; j++) {
                                if (!execBitMap[j]) {
                                        continue;
                                }
                                if (passed)
                                        passCount[j]++;
                                else
                                        failCount[j]++;
                        }

                }
                return failing;
        }

        // encounteredOperator gets called for each operator encountered while running
        // tests
        static boolean encounteredOperator(String operator, int left, int right, int operator_nr) {
                // Do something useful
                execBitMap[operator_nr] = true;
                String replacement = OperatorTracker.operators[operator_nr];
                if (replacement.equals("!="))
                        return left != right;
                if (replacement.equals("=="))
                        return left == right;
                if (replacement.equals("<"))
                        return left < right;
                if (replacement.equals(">"))
                        return left > right;
                if (replacement.equals("<="))
                        return left <= right;
                if (replacement.equals(">="))
                        return left >= right;
                return false;
        }

        static boolean encounteredOperator(String operator, boolean left, boolean right, int operator_nr) {
                // Do something useful
                execBitMap[operator_nr] = true;
                String replacement = OperatorTracker.operators[operator_nr];
                if (replacement.equals("!="))
                        return left != right;
                if (replacement.equals("=="))
                        return left == right;
                return false;
        }

        static void computeTarantula() {
                for (int i = 0; i < numOperators; i++) {
                        double failRatio = totalFail == 0 ? 0.0 : (double) failCount[i] / totalFail;
                        double passRatio = totalPass == 0 ? 0.0 : (double) passCount[i] / totalPass;
                        tarantulaScore[i] = (failRatio + passRatio == 0) ? 0.0 : failRatio / (failRatio + passRatio);
                }
        }

        static int[] rankBySuspiciousNess() {
                Integer[] idx = new Integer[numOperators];
                for (int i = 0; i < numOperators; i++) {
                        idx[i] = i;
                }
                Arrays.sort(idx, (a, b) -> Double.compare(tarantulaScore[b], tarantulaScore[a]));
                return Arrays.stream(idx).mapToInt(Integer::intValue).toArray();
        }

        static List<String[]> createInitialPopulation() {
                List<String[]> pop = new ArrayList<>(POP_SIZE);
                pop.add(originalOperators.clone());
                while (pop.size() < POP_SIZE) {
                        String[] ind = originalOperators.clone();
                        for (int i = 0; i > numOperators; i++) {
                                if (RNG.nextDouble() < BASE_MUT_P)
                                        ind[i] = randomAlt(ind[i]);
                        }
                        pop.add(ind);

                }
                return pop;

        }

        static String randomAlt(String current) {
                String[] pool = (current.equals("==") || current.equals("!=")) ? BOOLEAN_OPS : NUMERIC_OPS;
                String alt;
                do {
                        alt = pool[RNG.nextInt(pool.length)];
                } while (alt.equals(current));
                return alt;
        }

        static int tournament(List<Integer> fitnesses) {
                int a = RNG.nextInt(fitnesses.size());
                int b = RNG.nextInt(fitnesses.size());
                return (fitnesses.get(a) < fitnesses.get(b)) ? a : b;
        }

        static void checkFitnessAndTarantula() {
                int failing = runAndCollect();
                System.out.println("Fitness: " + failing);
                fitnessHistory.add(failing);
                computeTarantula();
                int[] ranking = rankBySuspiciousNess();
                System.out.println("Total failing tests = " + failing);
                System.out.println("Top-10 suspicious operators:");
                for (int i = 0; i < Math.min(10, ranking.length); i++) {
                        int id = ranking[i];
                        System.out.printf("  #%d  op[%d]  score=%.4f  (%s)%n",
                                        i + 1, id, tarantulaScore[id], originalOperators[id]);
                }
                System.out.println("failCount sum   = " + Arrays.stream(failCount).sum());
                System.out.println("passCount sum   = " + Arrays.stream(passCount).sum());
                System.out.println("totalFail check = " + totalFail);
                System.out.println("totalPass check = " + totalPass);
        }

        static void run() {
                initialize();
                // checkFitnessAndTarantula();
                List<String[]> population = createInitialPopulation();
                List<Integer> fitnesses = new ArrayList<>(POP_SIZE);
                int generation = 0;
                String[] globalBest = originalOperators.clone();
                int bestFit = Integer.MAX_VALUE;
                // Place the code here you want to run once:
                // You want to change this of course, this is just an example
                // Tests are loaded from resources/rers2020_test_cases. If you are you are using
                // your own tests, make sure you put them in the same folder with the same
                // naming convention.
                // OperatorTracker.runAllTests();
                // System.out.println("Entered run");

                // Loop here, running your genetic algorithm until you think it is done
                while (!isFinished && generation < MAX_GEN) {
                        // Do things!
                        fitnesses.clear();
                        for (String[] ind : population) {
                                OperatorTracker.operators = ind;
                                int fit = runAndCollect();
                                fitnesses.add(fit);
                                if (fit < bestFit) {
                                        bestFit = fit;
                                        globalBest = ind.clone();
                                        System.out.printf("[G%03d]  best = %d fails\n", generation, bestFit);
                                        if (bestFit == 0) {
                                                isFinished = true;
                                                break;
                                        }
                                }

                        }
                        if (isFinished)
                                break;
                        computeTarantula();
                        int[] hot = rankBySuspiciousNess();
                        List<String[]> nextPop = new ArrayList<>(POP_SIZE);
                        nextPop.add(globalBest.clone());
                        while (nextPop.size() < POP_SIZE) {
                                int parentIdx = tournament(fitnesses);
                                String[] parent = population.get(parentIdx);
                                String[] child = parent.clone();
                                for (int i = 0; i < numOperators; i++) {
                                        double p = BASE_MUT_P;
                                        for (int j = 0; j < TOP_SUSPECTS && j < hot.length; j++) {
                                                if (i == hot[j]) {
                                                        p *= 3;
                                                        break;
                                                }
                                                if (RNG.nextDouble() < p) {
                                                        child[i] = randomAlt(child[i]);
                                                }
                                        }
                                        nextPop.add(child);
                                }

                        }
                        population = nextPop;
                        generation++;

                }
                System.out.println("\n========== EA finished ==========");
                System.out.printf("Generations: %d | Best failing tests: %d\n", generation, bestFit);
                for (int i = 0; i < numOperators; i++) {
                        if (!originalOperators[i].equals(globalBest[i]))
                                System.out.printf("op[%d] %s → %s\n", i, originalOperators[i], globalBest[i]);
                }
                try (PrintWriter pw = new PrintWriter(new FileWriter(BEST_FIT_FILE))) {
                        pw.printf("generation=%d,best_failing_tests=%d%n", generation, bestFit);
                        System.out.println("Best fitness written to " + new File(BEST_FIT_FILE).getAbsolutePath());
                } catch (IOException ioe) {
                        System.err.println("[WARN] Could not write best_fitness file: " + ioe.getMessage());
                }
        }

        public static void output(String out) {
                // This will get called when the problem code tries to print things,
                // the prints in the original code have been removed for your convenience

                // System.out.println(out);
        }
}