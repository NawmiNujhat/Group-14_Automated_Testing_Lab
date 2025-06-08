package nl.tudelft.instrumentation.patching;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.text.SimpleDateFormat;
import java.util.*;
import java.util.stream.IntStream;

public class PatchingLab {

        static Random r = new Random();
        static boolean isFinished = false;
        static int numOperators;
        static double[] tarantulaScore;
        static String[] originalOperators;
        private static final String BEST_FIT_FILE = "best_fitness.txt";
        private static final String BEST_FIT_OVER_TIME_FILE = "best_fitness_over_time.csv";
        static int numField;
        static boolean[] execBitMap;
        private static Map<Integer, Integer> fitnessOverTime = new HashMap<Integer, Integer>();
        private static int[] passCount;
        private static int[] failCount;
        private static int totalPass, totalFail;
        private static final Random RNG = new Random();
        private static final int POP_SIZE = 50;
        private static final int MAX_GEN = 500;
        private static final double BASE_MUT_P = 0.05;
        private static final int TOP_SUSPECTS = 5;
        private static final String[] NUMERIC_OPS = { ">", "<", ">=", "<=", "==", "!=" };
        private static final String[] BOOLEAN_OPS = { "==", "!=" };
        static final int TIME_BUDGET_MS = 30 * 60 * 1000;

        static final List<Integer> fitnessHistory = new ArrayList<>();

        private static final int STAGNATE_GENS = 10;
        private static int lastImprovementGen = 0;
        private static int prevBest = Integer.MAX_VALUE;
        private static final double P_SWAP = 0.25;
        private static final double P_DELETE = 0.25;
        private static final double P_INSERT = 0.25;
        private static final double P_CHANGE = 0.25;
        private static final int PROBLEM_ID = 15;

        private static double annealAdaptive(int generation, int currentBest) {
                // track when we last saw an improvement
                if (currentBest < prevBest) {
                        prevBest = currentBest;
                        lastImprovementGen = generation;
                }
                // base linear decay
                double base = 0.30 - (0.29 * generation / (MAX_GEN - 1)); // from .30 → .01

                // if stuck for too long, inject a “restart” spike
                int stuck = generation - lastImprovementGen;
                if (stuck > STAGNATE_GENS) {
                        // ramp back to 30% then continue decay
                        double overshoot = Math.min(1.0, (double) (stuck - STAGNATE_GENS) / STAGNATE_GENS);
                        return base + (0.30 - base) * overshoot;
                }
                return base;
        }
      
        static String[] complexMutate(String[] parent) {
                // work on a List so we can add/remove
                List<String> genes = new ArrayList<>(Arrays.asList(parent));
                double r = RNG.nextDouble();

                if (r < P_SWAP) {
                        // 1) swap two random positions
                        if (genes.size() >= 2) {
                                int i = RNG.nextInt(genes.size());
                                int j = RNG.nextInt(genes.size());
                                Collections.swap(genes, i, j);
                        }

                } else if (r < P_SWAP + P_DELETE) {
                        // 2) delete one random gene (if size > 1)
                        if (genes.size() > 1) {
                                genes.remove(RNG.nextInt(genes.size()));
                        }

                } else if (r < P_SWAP + P_DELETE + P_INSERT) {
                        // 3) insert a brand‐new (randomAlt) gene at random position
                        String template = originalOperators[RNG.nextInt(numOperators)];
                        String newOp = randomAlt(template);
                        int pos = RNG.nextInt(genes.size() + 1);
                        genes.add(pos, newOp);

                } else {
                        // 4) change one gene in place (your old randomAlt)
                        int i = RNG.nextInt(genes.size());
                        genes.set(i, randomAlt(genes.get(i)));
                }

                // if you really need a fixed length, you can now
                // either truncate or pad back to parent.length:
                while (genes.size() < parent.length) {
                        // pad with a random pick
                        genes.add(randomAlt(originalOperators[RNG.nextInt(numOperators)]));
                }
                if (genes.size() > parent.length) {
                        genes = genes.subList(0, parent.length);
                }

                return genes.toArray(new String[0]);
        }

        static void initialize() {
                // initialize the population based on OperatorTracker.operators
                originalOperators = OperatorTracker.operators.clone();
                numOperators = originalOperators.length;
                passCount = new int[numOperators];
                failCount = new int[numOperators];
                execBitMap = new boolean[numOperators];
                tarantulaScore = new double[numOperators];

        }

        static int runAndCollect() {
                Arrays.fill(passCount, 0);
                Arrays.fill(failCount, 0);
                totalPass = totalFail = 0;
                int nTests = OperatorTracker.tests.size();
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
                        for (int i = 0; i < numOperators; i++) {
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

        static int rouletteWheelSelect(List<Integer> fitnesses) {
                // compute weights = 1/(f+1)
                double total = 0;
                double[] weights = new double[fitnesses.size()];
                for (int i = 0; i < fitnesses.size(); i++) {
                        weights[i] = 1.0 / (fitnesses.get(i) + 1);
                        total += weights[i];
                }
                // spin
                double spin = RNG.nextDouble() * total;
                double cum = 0;
                for (int i = 0; i < weights.length; i++) {
                        cum += weights[i];
                        if (cum >= spin)
                                return i;
                }
                return weights.length - 1;
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
                Random rand = RNG;
                long deadline = System.currentTimeMillis() + TIME_BUDGET_MS;
                long start = System.currentTimeMillis();
                // Place the code here you want to run once:
                // You want to change this of course, this is just an example
                // Tests are loaded from resources/rers2020_test_cases. If you are you are using
                // your own tests, make sure you put them in the same folder with the same
                // naming convention.
                // OperatorTracker.runAllTests();
                // System.out.println("Entered run");

                // Loop here, running your genetic algorithm until you think it is done
                while (System.currentTimeMillis() < deadline && (!isFinished && generation<MAX_GEN)) {
                        System.out.println("Generation: " + generation);
                        // Do things!
                        int genBest = Integer.MAX_VALUE;
                        fitnesses.clear();
                        for (String[] ind : population) {
                                OperatorTracker.operators = ind;
                                int fit = runAndCollect();
                                fitnesses.add(fit);
                                System.out.println("Fit: " + fit);
                                genBest = Math.min(genBest, fit);
                                System.out.println("Gen Best: " + genBest);
                                if (fit < bestFit) {
                                        // Update best fit and store timestamp
                                        bestFit = fit;
                                        globalBest = ind.clone();
                                        fitnessOverTime.put((int) (long) (System.currentTimeMillis() - start) / 1000, bestFit);

                                        if (bestFit == 0) {
                                                isFinished = true;
                                                break;
                                        }
                                }

                        }
                        if (isFinished)
                                break;
                        // System.out.println("Best Fit: " + bestFit);
                        OperatorTracker.operators = globalBest;
                        runAndCollect();
                        computeTarantula();
                        int[] hot = rankBySuspiciousNess();
                        System.out.printf("[G%03d] gen-best=%d   overall-best=%d%n",
                                        generation, genBest, bestFit);
                        List<String[]> nextPop = new ArrayList<>(POP_SIZE);
                        nextPop.add(globalBest.clone());
                        while (nextPop.size() < POP_SIZE) {
                                // pick two parents
                                int p1 = rouletteWheelSelect(fitnesses);
                                int p2 = rouletteWheelSelect(fitnesses);
                                String[] mom = population.get(p1);
                                String[] dad = population.get(p2);
                                double baseM = annealAdaptive(generation, bestFit);

                                // uniform‐crossover then mutate
                                String[] child = new String[numOperators];
                                for (int i = 0; i < numOperators; i++) {
                                        // pick gene from mom or dad
                                        child[i] = RNG.nextBoolean() ? mom[i] : dad[i];

                                        // mutation (boosted if in top suspects)

                                        boolean isHot = false;
                                        for (int j = 0; j < TOP_SUSPECTS; j++) {

                                                if (hot[j] == i) {
                                                        isHot = true;
                                                        break;
                                                }

                                        }
                                        // double mProb = baseM + (isHot ? baseM * 2 : 0);
                                        

                                }
                                child=complexMutate(child);
                                nextPop.add(child);
                        }

                        population = nextPop;
                        generation++;
                }
                System.out.println("Finished after: " + ((System.currentTimeMillis() - start) / 1000) + "s");
                System.out.println("\n========== EA finished ==========");
                System.out.printf("Generations: %d | Best failing tests: %d\n", generation, bestFit);
                for (int i = 0; i < numOperators; i++) {
                        if (!originalOperators[i].equals(globalBest[i]))
                                System.out.printf("op[%d] %s → %s\n", i, originalOperators[i], globalBest[i]);
                }
                try (PrintWriter pw = new PrintWriter(new FileWriter(BEST_FIT_FILE,true))) {
                        pw.printf("generation=%d,best_failing_tests=%d%n", generation, bestFit);
                        System.out.println("Best fitness written to " + new File(BEST_FIT_FILE).getAbsolutePath());
                } catch (IOException ioe) {
                        System.err.println("[WARN] Could not write best_fitness file: " + ioe.getMessage());
                }
                try (PrintWriter out = new PrintWriter(new FileWriter("best_patch.txt",true))) {
                        for (int i = 0; i < numOperators; i++) {
                                if (!originalOperators[i].equals(globalBest[i])) {
                                        out.printf("op[%d]  %s  →  %s%n",
                                                        i, originalOperators[i], globalBest[i]);
                                }
                        }
                } catch (IOException ioe) {
                        System.err.println("[WARN] Could not write best_patch file: " + ioe.getMessage());
                }

                // Best fitness over time
                saveFitnessOverTimeCSV();
        }

        static void saveFitnessOverTimeCSV() {
                String filename = "lab_3_fitness/fitness_over_time_" + PROBLEM_ID + ".csv";
                Map<Integer, Integer> sortedFitness = new TreeMap<>(fitnessOverTime);
                try (PrintWriter pw = new PrintWriter(new FileWriter(filename, true))) {
                        pw.println("Time (s), Best Fitness");
                        sortedFitness.forEach((key, value) -> pw.printf(key + ", " + value + "\n"));
                        System.out.println("Saved fitness over time to " + filename);
                } catch (IOException e) {
                        System.err.println("Error writing to file: " + e.getMessage());
                }
        }


        public static void output(String out) {
                // This will get called when the problem code tries to print things,
                // the prints in the original code have been removed for your convenience

                // System.out.println(out);
        }
}