package miners.test;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.net.URL;

import miners.algorithms.frequentpatterns.efim.AlgoEFIM;
import miners.algorithms.frequentpatterns.efim.Itemsets;

// dEFIM TESTER, OUTPUT TO SCREEN
public class testEFIM_mem {

	public static void main(String [] arg) throws IOException, InterruptedException {
		String input = "accidents.txt";	// the input and output file paths
		//int minutil = 12500000;					// the minutil threshold
		double sumUtil = 1.96141636E+8;
		int minutil =  (int) Math.round(sumUtil * 0.1);
		int dbSize = Integer.MAX_VALUE;//(1112949 * 100)/100;
		AlgoEFIM algo = new AlgoEFIM();				// Create the dEFIM algorithm object
		
		// execute the algorithm
		Itemsets itemsets = algo.runAlgorithm(minutil, input, null, true, dbSize, true);
		
		algo.printStats();							// Print statistics
		//itemsets.printItemsets();					// Print the itemsets
	}

}
