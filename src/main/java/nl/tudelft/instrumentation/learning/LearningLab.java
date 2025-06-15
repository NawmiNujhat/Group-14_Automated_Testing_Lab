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

        String expectedOutput = sul.getLastOutput(word); 

        // Get all expanded access sequences
        List<Word<String>> expandedAccess = observationTable.getExpandedAccessSequences();
        // Sort from shortest to longest to prioritize minimal prefixes
        expandedAccess.sort(Comparator.comparingInt(w -> w.asList().size()));

        List<Word<String>> accessSequences = observationTable.getAccessSequences();
        
        // Clone the counterexample
        Word<String> current = new Word(word.asList());  

        // Iterate over prefixes (expanded access sequences)
        for (int i = expandedAccess.size() - 1; i >= 0; i--) {
            Word<String> prefix = expandedAccess.get(i);

            if (current.toString().startsWith(prefix.toString())) {
                // Find a representative access sequence whose row matches that of the prefix
                for (Word<String> s : accessSequences) {
                    if (observationTable.getTableRow(prefix).equals(observationTable.getTableRow(s))) {
                        int prefixLength = prefix.asList().size();
                        List<String> suffix = current.asList().subList(prefixLength, current.asList().size());
                        Word<String> reconstructed = s.append(suffix);

                        // Check if reconstructed input behaves differently than original
                        if (!sul.getLastOutput(reconstructed).equals(expectedOutput)) {
                            // Return distinguishing suffix
                            return new Word<>(suffix);  
                        } else {
                            // Retry search with different prefix
                            i = expandedAccess.size();
                        }
                        break;
                    }
                }
            }
        }

        // No distinguishable suffix found
        return null;  
    }

    static void run() {

        SystemUnderLearn sul = new RersSUL();
        observationTable = new ObservationTable(LearningTracker.inputSymbols, sul);
        // equivalenceChecker = new RandomWalkEquivalenceChecker(sul, LearningTracker.inputSymbols, 100, 1000);
        equivalenceChecker = new WMethodEquivalenceChecker(sul, LearningTracker.inputSymbols, 1, observationTable, observationTable, 1000);

        observationTable.print();
        // Moved to updateHypothesis
        hypothesis = observationTable.generateHypothesis();
        hypothesis.writeToDot("hypothesis.dot");
        numStates = hypothesis.getStates().length;

        // Place here your code to learn a model of the RERS problem.
        // Implement the checks for consistent and closed in the observation table.
        // Use the observation table and the equivalence checker to implement the L* learning algorithm.
        while (!isFinished) {
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
