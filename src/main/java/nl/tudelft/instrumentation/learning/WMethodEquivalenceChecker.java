package nl.tudelft.instrumentation.learning;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Random;

public class WMethodEquivalenceChecker extends EquivalenceChecker{

    private int w;
    private AccessSequenceGenerator accessSequenceGenerator;
    private DistinguishingSequenceGenerator distinguishingSequenceGenerator;
    private Random r;
    private int numSamples;

    public WMethodEquivalenceChecker(SystemUnderLearn sul, String[] inputSymbols, int w, DistinguishingSequenceGenerator dg, AccessSequenceGenerator ag, int numSamples) {
        super(sul, inputSymbols);
        this.w = w;
        this.distinguishingSequenceGenerator= dg;
        this.accessSequenceGenerator= ag;
        this.numSamples = numSamples;
        this.r = new Random();
    }

    @Override
    public Optional<Word<String>> verify(MealyMachine hypothesis) {
        List<Word<String>> accessSequences = accessSequenceGenerator.getAccessSequences();
        List<Word<String>> distinguishingSequences = distinguishingSequenceGenerator.getDistinguishingSequences();

        for (int i = 0; i < numSamples; i++) {
            Word<String> a = getRandomElement(accessSequences);
            Word<String> d = getRandomElement(distinguishingSequences);
            Word<String> z = generateRandomWord(w);

            // Create string based on W-method
            Word<String> azd = a.append(z).append(d);

            String[] modelResult = hypothesis.getOutput(azd);
            String[] actualResult = sul.getOutput(azd);

            for (int j = 0; j < modelResult.length; j++) {
                if (!modelResult[j].equals(actualResult[j])) {
                    Word<String> counterExample = new Word<>(azd.asList().subList(0, j + 1));
                    return Optional.of(counterExample);
                }
            }
        }

        return Optional.empty();
    }

    private Word<String> getRandomElement(List<Word<String>> list) {
        System.out.println(list);
        System.out.println(list.size());
        System.out.println();
        return list.get(r.nextInt(list.size()));
    }

    private Word<String> generateRandomWord(int length) {
        List<String> symbols = new ArrayList<>(length);
        for (int i = 0; i < length; i++) {
            symbols.add(inputSymbols[r.nextInt(inputSymbols.length)]);
        }
        return new Word<>(symbols);
    }
}
