package nl.tudelft.instrumentation.learning;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;

/**
 * You should write your own solution using this class.
 */
public class LearningLab {
    static Random r = new Random();
    static int traceLength = 10;
    static boolean isFinished = false;

    static ObservationTable observationTable;
    static EquivalenceChecker equivalenceChecker;
    static MealyMachine hypothesis;
    static int numStates;
    static List<Word<String>> counterExampleList = new ArrayList<>();

    static final long startTime = System.currentTimeMillis();
    static final int PROBLEM_ID = 1;
    static final String OUTPUT_FILE = "lab_4_output/output_" + PROBLEM_ID + ".csv";

    private static void makeTableClosedAndConsistent() throws InterruptedException {
        boolean closed = false;
        boolean consistent = false;

        while (!(closed && consistent)) {
            closed = observationTable.checkForClosed()
                .map(w -> { observationTable.addToS(w); return false; })
                .orElse(true);

            consistent = observationTable.checkForConsistent()
                .map(w -> { observationTable.addToE(w); return false; })
                .orElse(true);

            if (!consistent) {
                closed = false;
            }

            updateHypothesis();
        }
    }

    private static void updateHypothesis() {
        hypothesis = observationTable.generateHypothesis();
        hypothesis.writeToDot("hypothesis.dot");

        if (hypothesis.getStates().length > numStates) {
            int timeElapsed = (int) (long) (System.currentTimeMillis() - startTime) / 1000;
            numStates = hypothesis.getStates().length;

            // Append to output
            try (PrintWriter pw = new PrintWriter(new FileWriter(OUTPUT_FILE, true))) {
                pw.println("Time (s), Best Fitness \n");
                pw.printf(timeElapsed + ", " + numStates + "\n");
                System.out.println("Saved fitness over time to " + OUTPUT_FILE);
            } 
            catch (IOException e) {
                System.err.println("Error writing to file: " + e.getMessage());
            }
        }
    }

    private static Word<String> handleCounterExample(Word<String> word) {
        RersSUL sul = new RersSUL();

        // TODO: implement handling of counter example
        throw new UnsupportedOperationException("Unimplemented method 'handleCounterExample'");
    }

    static void run() {

        SystemUnderLearn sul = new RersSUL();
        observationTable = new ObservationTable(LearningTracker.inputSymbols, sul);
        equivalenceChecker = new RandomWalkEquivalenceChecker(sul, LearningTracker.inputSymbols, 100, 1000);
        // equivalenceChecker = new WMethodEquivalenceChecker(sul, LearningTracker.inputSymbols, 1, observationTable, observationTable);

        observationTable.print();
        // Moved to updateHypothesis
        hypothesis = observationTable.generateHypothesis();
        hypothesis.writeToDot("hypothesis.dot");
        numStates = hypothesis.getStates().length;

        // Place here your code to learn a model of the RERS problem.
        // Implement the checks for consistent and closed in the observation table.
        // Use the observation table and the equivalence checker to implement the L* learning algorithm.
        while (!isFinished) {
            // Do things!
            try {
                makeTableClosedAndConsistent();
                updateHypothesis();

                Optional<Word<String>> counterExample = equivalenceChecker.verify(hypothesis);
                if (counterExample.isPresent()) {
                    counterExampleList.add(counterExample.get());

                    Word<String> finalCounterExample = handleCounterExample(counterExample.get());
                    if (finalCounterExample == null) isFinished = true;

                    observationTable.addToE(finalCounterExample);
                } else {
                    isFinished = true;
                }
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        System.out.println("Final state count: " + hypothesis.getStates().length);
        System.out.println("Learning finished.");
    }


    /**
     * Method that is used for catching the output from standard out.
     * 
     * @param out the string that has been outputted in the standard out.
     */
    public static void output(String out) {
        // System.out.println(out);
    }
}
