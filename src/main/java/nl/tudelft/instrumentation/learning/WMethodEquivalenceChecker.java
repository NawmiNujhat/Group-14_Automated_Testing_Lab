package nl.tudelft.instrumentation.learning;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Random;

public class WMethodEquivalenceChecker extends EquivalenceChecker {

    private int w;
    private AccessSequenceGenerator accessSequenceGenerator;
    private DistinguishingSequenceGenerator distinguishingSequenceGenerator;
    private Random r;
    private int numSamples;

    public WMethodEquivalenceChecker(SystemUnderLearn sul, String[] inputSymbols, int w,
            DistinguishingSequenceGenerator dg, AccessSequenceGenerator ag, int numSamples) {
        super(sul, inputSymbols);
        this.w = w;
        this.distinguishingSequenceGenerator = dg;
        this.accessSequenceGenerator = ag;
        this.numSamples = numSamples;
        this.r = new Random();
    }

    @Override
    public Optional<Word<String>> verify(MealyMachine hypothesis) {
        List<Word<String>> accessSequences = accessSequenceGenerator.getAccessSequences();
        List<Word<String>> distinguishingSequences = distinguishingSequenceGenerator.getDistinguishingSequences();
        List<Word<String>> allZ = generateAllWordsUpToLength(w);
        int count = 0;
        int totalTests = accessSequences.size() * allZ.size() * distinguishingSequences.size();

        for (Word<String> a : accessSequences) {
            for (Word<String> z : allZ) {
                for (Word<String> d : distinguishingSequences) {
                    count++;
                    if (count % 1000 == 0) {
                        System.out.println("WMethod progress: " + count + " / " + totalTests + " tests done");
                    }
                    Word<String> testWord = a.append(z).append(d);

                    String[] modelOutput = hypothesis.getOutput(testWord);
                    String[] actualOutput = sul.getOutput(testWord);

                    for (int i = 0; i < modelOutput.length; i++) {
                        if (!modelOutput[i].equals(actualOutput[i])) {
                            Word<String> counterExample = new Word<>(testWord.asList().subList(0, i + 1));
                            return Optional.of(counterExample);
                        }
                    }
                }
            }
        }

        return Optional.empty();
    }

    // private Word<String> getRandomElement(List<Word<String>> list) {
    // System.out.println(list);
    // System.out.println(list.size());
    // System.out.println();
    // return list.get(r.nextInt(list.size()));
    // }

    // private Word<String> generateRandomWord(int length) {
    // List<String> symbols = new ArrayList<>(length);
    // for (int i = 0; i < length; i++) {
    // symbols.add(inputSymbols[r.nextInt(inputSymbols.length)]);
    // }
    // return new Word<>(symbols);
    // }

    private List<Word<String>> generateAllWordsUpToLength(int maxLength) {
        List<Word<String>> allWords = new ArrayList<>();
        allWords.add(new Word<>(new ArrayList<>())); // empty word ε

        for (int length = 1; length <= maxLength; length++) {
            generateWordsRecursive(new ArrayList<>(), length, allWords);
        }
        return allWords;
    }

    private void generateWordsRecursive(List<String> prefix, int length, List<Word<String>> collector) {
        if (length == 0) {
            collector.add(new Word<>(new ArrayList<>(prefix)));
            return;
        }
        for (String symbol : inputSymbols) {
            prefix.add(symbol);
            generateWordsRecursive(prefix, length - 1, collector);
            prefix.remove(prefix.size() - 1);
        }
    }

}
