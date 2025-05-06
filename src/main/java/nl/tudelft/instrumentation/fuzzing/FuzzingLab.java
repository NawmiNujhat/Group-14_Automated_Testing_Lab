package nl.tudelft.instrumentation.fuzzing;

import java.util.*;

import javax.sound.midi.SysexMessage;

/**
 * You should write your own solution using this class.
 */
public class FuzzingLab {
        static Random r = new Random();
        static List<String> currentTrace;
        static int traceLength = 10;
        static boolean isFinished = false;
        static Map<Integer, Double> latestBranchDistances = new HashMap<>();
        static Set<Integer> visitedBranches = new HashSet<>();
        static Set<String> discoveredErrorCodes = new HashSet<>();

        static final int MUTATIONS_PER_ITERATION = 5;
        static final int TIME_BUDGET_MS = 5*60*1000;
        static final double RESTART_PROBABILITY = 0.1;
        static final double K = 0.1;

        static void initialize(String[] inputSymbols){
                // Initialise a random trace from the input symbols of the problem.
                currentTrace = generateRandomTrace(inputSymbols);
        }
        
        /**
         * Write your solution that specifies what should happen when a new branch has been found.
         */
        static void encounteredNewBranch(MyVar condition, boolean value, int line_nr) {
                double raw=rawBranchDistance(condition,value);
                double normalizedDistance= normalize(raw);
                latestBranchDistances.put(line_nr,normalizedDistance);
                visitedBranches.add(line_nr);
                System.out.println("Branch at line " + line_nr + ": " + condition.toString() + 
                " evaluated as " + value + " with distance " + normalizedDistance);
                System.out.println(condition.toString());
        }
        static double normalize(double distance) {
                return distance / (distance + 1);
        }
        static double computeTotalDistance() {
                return latestBranchDistances.values().stream().mapToDouble(d -> d).sum();
            }
        
        static double rawBranchDistance(MyVar condition, boolean actualValue)
        {
                switch (condition.type)
                { 
                        case INT:
                        case BOOL:
                           if (condition.value==actualValue)
                           {
                                return 0.0;
                           }
                           else{
                              return 1.0;
                           }
                        case BINARY:
                           switch (condition.operator){
                                case "==":
                                  if(condition.left.type==TypeEnum.STRING && condition.right.type==TypeEnum.STRING)
                                   {
                                       String leftStr=condition.left.str_value;
                                       String rightStr=condition.right.str_value;
                                       return actualValue ? 0 : editDistance(leftStr, rightStr);
                                   }
                                  else{
                                        double leftval= condition.left.int_value;
                                        double rightval=condition.right.int_value;
                                        return actualValue ? 0 :Math.abs(leftval-rightval);
                                  }
                                case "!=":
                                  if(condition.left.type==TypeEnum.STRING && condition.right.type==TypeEnum.STRING){
                                       String leftStr=condition.left.str_value;
                                       String rightStr=condition.right.str_value;
                                       return actualValue ? 0 : (leftStr.equals(rightStr) ? 1 : 0);
                                  }
                                  else
                                  {
                                        double leftval= condition.left.int_value;
                                        double rightval=condition.right.int_value;
                                        double diff= Math.abs(leftval-rightval);
                                        return actualValue ? 0 : ((diff==0)?1:0);
                                  }
                                case "<":
                                        double leftval= condition.left.int_value;
                                        double rightval=condition.right.int_value;
                                        return actualValue ? 0 :Math.max(0,leftval-rightval+1);
                                case "<=":
                                        leftval= condition.left.int_value;
                                        rightval=condition.right.int_value;
                                        return actualValue ? 0 :Math.max(0,leftval-rightval);
                                case ">":
                                        leftval= condition.left.int_value;
                                        rightval=condition.right.int_value;
                                        return actualValue ? 0 :Math.max(0,rightval-leftval+1);
                                case ">=":
                                        leftval= condition.left.int_value;
                                        rightval=condition.right.int_value;
                                        return actualValue ? 0 :Math.max(0,rightval-leftval);
                                
                                case "&&":
                                case "&":
                                  if (actualValue){
                                        return 0.0;
                                  }
                                  else{
                                        double leftdist=rawBranchDistance(condition.left,true);
                                        double rightdist=rawBranchDistance(condition.right,true);
                                        return leftdist+rightdist;

                                  }
                                case "||":
                                case "|":
                                  if (actualValue){
                                        return 0.0;
                                  }
                                  else{
                                        double leftdist=rawBranchDistance(condition.left,true);
                                        double rightdist=rawBranchDistance(condition.right, true);
                                        return Math.min(leftdist,rightdist);

                                  }
                                case "^":
                                case "XOR":
                                  if (actualValue){
                                        return 0.0;
                                  }
                                  else{
                                        double d1=rawBranchDistance(condition.left,true)+ (1-rawBranchDistance(condition.right, false));
                                        double d2=rawBranchDistance(condition.right, true)+(1-rawBranchDistance(condition.left, false));
                                        return Math.min(d1,d2);

                                  }
                                
                                  default:
                                    return actualValue ?0.0:1.0;

                           }
                        case UNARY:
                          if(condition.operator.equals("!"))
                           {
                                return actualValue ? 0: (1-rawBranchDistance(condition, false));
                           }
                          return actualValue ? 0.0 :1.0;
                        default:
                          return actualValue ? 0 : 1;
                }

        }

        static int editDistance(String str1, String str2)
        {
                int m= str1.length();
                int n= str2.length();
                int [][] dp=new int[m+1][n+1];
                for (int i=0; i<=m;i++){
                    for(int j=0;j<=n;j++)
                    {
                        if(i==0)
                        {
                                dp[i][j]=j;
                        }
                        else if(j==0)
                        {
                                dp[i][j]=i;
                        }
                        else if (str1.charAt(i-1)==str2.charAt(j-1))
                        {
                                dp[i][j]=dp[i-1][j-1];
                        }
                        else{
                                dp[i][j]=1+Math.min(
                                        Math.min(dp[i][j-1],
                                        dp[i-1][j]),dp[i-1][j-1]);
                        }
                    }
                }
                return dp[m][n];
        }

        /**
         * Method for fuzzing new inputs for a program.
         * @param inputSymbols the inputSymbols to fuzz from.
         * @return a fuzzed sequence
         */
        static double calculateFitness(List<String>trace){
                latestBranchDistances.clear();
                int previousBranchCount=visitedBranches.size();
                DistanceTracker.runNextFuzzedSequence(trace.toArray(new String[0]));
                double sumDistances= 0.0;
                for(double distance:latestBranchDistances.values())
                {
                        sumDistances+=distance;
                }
                int newBranches=visitedBranches.size()-previousBranchCount;
                //For penalyt coefficient, 
                //sumDistances-=previousBranchCount*10;
                return sumDistances;
        }
        static List<String>mutateTrace(List<String>trace, String[] inputSymbols)
        {
                List<String>mutated=new ArrayList<>(trace);
                int mutationType=r.nextInt(4);
                switch (mutationType){
                        case 0:
                          if(mutated.size()>0){
                                int index=r.nextInt(mutated.size());
                                mutated.set(index,inputSymbols[r.nextInt(inputSymbols.length)]);
                          }
                          break;
                        case 1:
                          mutated.add(inputSymbols[r.nextInt(inputSymbols.length)]);
                        case 2:
                          if(mutated.size()>1)
                           {
                                int index=r.nextInt(mutated.size());
                                mutated.remove(index);
                           }
                           break;
                        case 3:
                           if(mutated.size()>1)
                           {
                                int index1= r.nextInt(mutated.size());
                                int index2= r.nextInt(mutated.size());
                                while(index2==index1)
                                {
                                        index2=r.nextInt(mutated.size());
                                }
                                String temp=mutated.get(index1);
                                mutated.set(index1,mutated.get(index2));
                                mutated.set(index2,temp);

                           }
                           break;
                }
           return mutated;

        }
        static List <String> hillClimbing(String[] inputSymbols)
        {
                List <String> bestTrace= new ArrayList <> (currentTrace);
                double bestFitness=calculateFitness(bestTrace);
                boolean improved=false;
                for(int i=0;i<MUTATIONS_PER_ITERATION;i++){
                        List<String> mutatedTrace=mutateTrace(bestTrace,inputSymbols);
                        double mutatedFitness=calculateFitness(mutatedTrace);
                        if(mutatedFitness<bestFitness){
                                bestTrace=mutatedTrace;
                                bestFitness=mutatedFitness;
                                System.out.println("Found Better trace with Fitness: "+bestFitness+", branches: "+visitedBranches.size());
                                improved=true;
                        }
                }
                if(!improved)
                {
                   bestTrace=generateRandomTrace(inputSymbols);
                }
                return bestTrace;

        }
        static List<String> fuzz(String[] inputSymbols){
                /*
                 * Add here your code for fuzzing a new sequence for the RERS problem.
                 * You can guide your fuzzer to fuzz "smart" input sequences to cover
                 * more branches. Right now we just generate a complete random sequence
                 * using the given input symbols. Please change it to your own code.
                 */
                // return generateRandomTrace(inputSymbols);
                return hillClimbing(inputSymbols);
        }

        /**
         * Generate a random trace from an array of symbols.
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
                DistanceTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));

                // Place here your code to guide your fuzzer with its search.
                int noImprovementCounter=0;
                int previousBranchCount=0;
                long deadline = System.currentTimeMillis() + TIME_BUDGET_MS;
                System.out.println("Starting fuzzing with hill climbing...");

                while(!isFinished) {
                        // Do things!
                                while(System.currentTimeMillis()<deadline)
                                {
                                        currentTrace= fuzz(DistanceTracker.inputSymbols);
                                        System.out.printf("Covered %d branches, found %d error codes\n",
                                        visitedBranches.size(), discoveredErrorCodes.size());
                                        previousBranchCount=visitedBranches.size();
                                        if(visitedBranches.size()<=previousBranchCount)
                                        {
                                                noImprovementCounter++;
                                        }
                                        System.out.printf("No Improvement found in %d cases",noImprovementCounter);
                                }
                                System.out.printf("Time's up! Unique branches: %d, error codes: %d\n",
                                 visitedBranches.size(), discoveredErrorCodes.size());
                                 System.out.println("Error codes: " + discoveredErrorCodes);
                                 isFinished = true;
                }
        }

        /**
         * Method that is used for catching the output from standard out.
         * You should write your own logic here.
         * @param out the string that has been outputted in the standard out.
         */
        public static void output(String out){
                System.out.println(out);
                if(out.contains("error") || out.contains("Error"))
                {
                        discoveredErrorCodes.add(out);
                }
        }
}
