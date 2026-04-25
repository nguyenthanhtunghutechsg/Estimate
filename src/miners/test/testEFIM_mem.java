package miners.test;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.net.URL;

import miners.algorithms.frequentpatterns.efim.AlgoEFIM;
import miners.algorithms.frequentpatterns.efim.Itemsets;

// dEFIM TESTER, OUTPUT TO SCREEN
public class testEFIM_mem {

	public static void main(String [] arg) throws IOException, InterruptedException {
		String input = "chainstore.txt";	// the input and output file paths
		//int minutil = 12500000;					// the minutil threshold
		int minutil =  1_500_000;
		int dbSize = Integer.MAX_VALUE;//(1112949 * 100)/100;
		AlgoEFIM algo = new AlgoEFIM();				// Create the dEFIM algorithm object
		
		// execute the algorithm
		Itemsets itemsets = algo.runAlgorithm(minutil, input, null, true, dbSize, true);
		
		algo.printStats();							// Print statistics
		//itemsets.printItemsets();					// Print the itemsets
	}

}
