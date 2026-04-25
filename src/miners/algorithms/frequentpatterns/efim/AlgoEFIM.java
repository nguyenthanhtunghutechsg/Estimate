package   miners.algorithms.frequentpatterns.efim;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.lang.management.*;

import miners.tools.MemoryLogger;


/* This file is copyright (c) 2012-2015 Souleymane Zida & Philippe Fournier-Viger
 *
 * This file is part of the SPMF DATA MINING SOFTWARE
 * (http://www.philippe-fournier-viger.com/spmf).
 *
 * SPMF is free software: you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, either version 3 of the License, or (at your option) any later
 * version.
 * SPMF is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU General Public License for more details.
 * You should have received a copy of the GNU General Public License along with
 * SPMF. If not, see <http://www.gnu.org/licenses/>.
 */

/**
 * This is an implementation of the EFIM algorithm for
 * mining high-utility itemsets from a transaction database.
 * More information on the EFIM algorithm can be found in that paper: <br\>
 *
 * @author Souleymane Zida, Philippe Fournier-Viger using some code by Alan Souza
 */
public class AlgoEFIM {

    /** the set of high-utility itemsets */
    //private Itemsets highUtilityItemsets;

    /** object to write the output file */
    BufferedWriter writer = null;

    /** the number of high-utility itemsets found (for statistics) */
    private int patternCount;

    /** the start time and end time of the last algorithm execution */
    long startTimestamp;
    long endTimestamp;

    /** the minutil threshold */
    int minUtil;

    /** if this variable is set to true, some debugging information will be shown */
    final boolean  DEBUG = false;

    /** The following variables are the utility-bins array
     // Recall that each bucket correspond to an item */
    /** utility bin array for sub-tree utility */
    private int[] utilityBinArraySU;
    /** utility bin array for local utility */
    private int[] utilityBinArrayLU;

    /** a temporary buffer */
    private int [] temp= new int [500];

    /** The total time spent for performing intersections */
    long timeIntersections;
    /** The total time spent for performing database reduction */
    long timeDatabaseReduction;
    /** The total time spent for identifying promising items */
    long timeIdentifyPromisingItems;
    /** The total time spent for sorting */
    long timeSort;
    /** The total time spent for binary search */
    long timeBinarySearch;


    /** an array that map an old item name to its new name */
    int[] oldNameToNewNames;
    /** an array that map a new item name to its old name */
    int[] newNamesToOldNames;
    /** the number of new items */
    int newItemCount;

    /** if true, transaction merging will be performed by the algorithm */
    boolean activateTransactionMerging;

    /** A parameter for transaction merging*/
    final int MAXIMUM_SIZE_MERGING = 1000;

    /** number of times a transaction was read */
    long transactionReadingCount;
    /** number of merges */
    long mergeCount;

    /** number of itemsets from the search tree that were considered */
    private long candidateCount;

    /** If true, sub-tree utility pruning will be performed */
    private boolean activateSubtreeUtilityPruning;

    /**
     * Constructor
     */
    public AlgoEFIM() {

    }

    /**
     * Run the algorithm
     * @param minUtil  the minimum utility threshold (a positive integer)
     * @param inputPath  the input file path
     * @param outputPath  the output file path to save the result or null if to be kept in memory
     * @param activateTransactionMerging
     * @param activateSubtreeUtilityPruning
     * @param maximumTransactionCount
     * @return the itemsets or null if the user choose to save to file
     * @throws IOException if exception while reading/writing to file
     */
    /** Estimated payload memory before filtering (items + utilities only) */
    private long estimatedInitialDatabasePayloadBytes;
    /** Estimated payload memory removed by weak items (items + utilities only) */
    private long estimatedRemovedDatabasePayloadBytes;
    /** Estimated payload memory after filtering (items + utilities only) */
    private long estimatedReducedDatabasePayloadBytes;
    /** Total occurrences before filtering */
    private long totalItemOccurrences;
    /** Total occurrences removed by TWU filtering */
    private long removedItemOccurrences;
    /** Total occurrences kept after TWU filtering */
    private long keptItemOccurrences;

    /** support của item sau khi đổi tên theo thứ tự TWU */
    private int[] renamedItemSupport;

    /** độ dài trung bình của giao dịch sau khi lọc item yếu, giữ dạng double, ví dụ 8.5 */
    private double averageReducedTransactionLength;

    /** thống kê ước lượng projected DB trước lần đệ quy đầu tiên */
    private long estimatedFirstRecursionMemoryBytesMax;
    private long estimatedFirstRecursionSupportMin = Long.MAX_VALUE;
    private long estimatedFirstRecursionSupportMax;
    private int estimatedFirstRecursionMaxItem = -1;
    private double estimatedFirstRecursionMaxAvgRemainingLength;

    /** memory snapshots trước lần đệ quy đầu tiên */
    private long usedHeapBeforeFirstRecursionAfterGc;
    private long availableHeapBeforeFirstRecursionAfterGc;

    /** thống kê ước lượng trong đệ quy */
    private long estimatedRecursiveMemoryBytesMax;
    private int estimatedRecursiveMaxItem = -1;
    private int estimatedRecursiveMaxDepth = -1;
    private long estimatedRecursiveMaxSupport;
    private double estimatedRecursiveMaxAvgRemainingLength;
    private long estimatedRecursiveEstimateCount;

    /**
     * Statistics gathered during phase 1 without building the Dataset in memory.
     */
    private static final class Phase1Stats {
        int maxItem = 0;
        long totalUtility = 0L;
        int transactionCount = 0;
        long totalItemOccurrences = 0L;
        int[] twu;
        int[] support;


        Phase1Stats(int maxItem) {
            this.maxItem = maxItem;
            this.twu = new int[maxItem + 1];
            this.support = new int[maxItem + 1];
        }
    }

    /**
     * Parse one line of the input database and update phase-1 statistics.
     */
    private void processLineForPhase1(String line, Phase1Stats stats) {
        String[] split = line.split(":");
        int transactionUtility = Integer.parseInt(split[1]);
        String[] itemsString = split[0].split(" ");

        stats.transactionCount++;
        stats.totalUtility += transactionUtility;
        stats.totalItemOccurrences += itemsString.length;

        for (String itemString : itemsString) {
            int item = Integer.parseInt(itemString);
            stats.twu[item] += transactionUtility;
            stats.support[item]++;
        }
    }

    /**
     * Phase 1: scan the file to compute TWU and support without building the Dataset.
     */
    private Phase1Stats phase1ScanStats(String inputPath, int maximumTransactionCount) throws IOException {
        int maxItem = 0;

        try (BufferedReader br = new BufferedReader(new FileReader(inputPath))) {
            String line;
            int count = 0;
            while ((line = br.readLine()) != null) {
                if (line.isEmpty() || line.charAt(0) == '#' || line.charAt(0) == '%' || line.charAt(0) == '@') {
                    continue;
                }
                count++;
                String[] split = line.split(":");
                String[] itemsString = split[0].split(" ");
                for (String itemString : itemsString) {
                    int item = Integer.parseInt(itemString);
                    if (item > maxItem) {
                        maxItem = item;
                    }
                }
                if (count == maximumTransactionCount) {
                    break;
                }
            }
        }

        Phase1Stats stats = new Phase1Stats(maxItem);

        try (BufferedReader br = new BufferedReader(new FileReader(inputPath))) {
            String line;
            int count = 0;
            while ((line = br.readLine()) != null) {
                if (line.isEmpty() || line.charAt(0) == '#' || line.charAt(0) == '%' || line.charAt(0) == '@') {
                    continue;
                }
                count++;
                processLineForPhase1(line, stats);
                if (count == maximumTransactionCount) {
                    break;
                }
            }
        }
        return stats;
    }

    /**
     * Phase 2: read the file again and directly build the reduced/renamed dataset.
     */
    private Dataset buildReducedDataset(String inputPath, int maximumTransactionCount) throws IOException {
        Dataset dataset = new Dataset();

        try (BufferedReader br = new BufferedReader(new FileReader(inputPath))) {
            String line;
            int count = 0;
            while ((line = br.readLine()) != null) {
                if (line.isEmpty() || line.charAt(0) == '#' || line.charAt(0) == '%' || line.charAt(0) == '@') {
                    continue;
                }
                count++;

                String[] split = line.split(":");
                int transactionUtility = Integer.parseInt(split[1]);
                String[] itemsString = split[0].split(" ");
                String[] itemsUtilitiesString = split[2].split(" ");

                int length = itemsString.length;
                if (Transaction.tempItems.length < length) {
                    Transaction.tempItems = new int[length];
                    Transaction.tempUtilities = new int[length];
                }

                int keptCount = 0;
                int newTransactionUtility = transactionUtility;

                for (int i = 0; i < length; i++) {
                    int oldItem = Integer.parseInt(itemsString[i]);
                    int utility = Integer.parseInt(itemsUtilitiesString[i]);
                    int newItem = oldNameToNewNames[oldItem];

                    if (newItem != 0) {
                        Transaction.tempItems[keptCount] = newItem;
                        Transaction.tempUtilities[keptCount] = utility;
                        keptCount++;
                    } else {
                        newTransactionUtility -= utility;
                    }
                }

                if (keptCount > 0) {
                    int[] items = new int[keptCount];
                    int[] utilities = new int[keptCount];
                    System.arraycopy(Transaction.tempItems, 0, items, 0, keptCount);
                    System.arraycopy(Transaction.tempUtilities, 0, utilities, 0, keptCount);
                    Transaction.insertionSort(items, utilities);
                    dataset.addTransaction(new Transaction(items, utilities, newTransactionUtility));
                    dataset.sumLength+=items.length;
                }

                if (count == maximumTransactionCount) {
                    break;
                }
            }
        }

        return dataset;
    }

    /**
     * Run the algorithm
     * @param minUtil  the minimum utility threshold (a positive integer)
     * @param inputPath  the input file path
     * @param outputPath  the output file path to save the result or null if to be kept in memory
     * @param activateTransactionMerging
     * @param activateSubtreeUtilityPruning
     * @param maximumTransactionCount
     * @return the itemsets or null if the user choose to save to file
     * @throws IOException if exception while reading/writing to file
     */
    public Itemsets runAlgorithm(int minUtil, String inputPath, String outputPath, boolean activateTransactionMerging, int maximumTransactionCount, boolean activateSubtreeUtilityPruning) throws IOException {

        // reset variables for statistics
        mergeCount=0;
        transactionReadingCount=0;
        timeIntersections = 0;
        timeDatabaseReduction = 0;
        timeIdentifyPromisingItems = 0;
        timeSort = 0;
        timeBinarySearch = 0;
        candidateCount = 0;
        estimatedInitialDatabasePayloadBytes = 0L;
        estimatedRemovedDatabasePayloadBytes = 0L;
        estimatedReducedDatabasePayloadBytes = 0L;
        totalItemOccurrences = 0L;
        removedItemOccurrences = 0L;
        keptItemOccurrences = 0L;
        averageReducedTransactionLength = 0.0;
        estimatedFirstRecursionMemoryBytesMax = 0L;
        estimatedFirstRecursionSupportMin = Long.MAX_VALUE;
        estimatedFirstRecursionSupportMax = 0L;
        estimatedFirstRecursionMaxItem = -1;
        estimatedFirstRecursionMaxAvgRemainingLength = 0.0;
        usedHeapBeforeFirstRecursionAfterGc = 0L;
        availableHeapBeforeFirstRecursionAfterGc = 0L;
        estimatedRecursiveMemoryBytesMax = 0L;
        estimatedRecursiveMaxItem = -1;
        estimatedRecursiveMaxDepth = -1;
        estimatedRecursiveMaxSupport = 0L;
        estimatedRecursiveMaxAvgRemainingLength = 0.0;
        estimatedRecursiveEstimateCount = 0L;

        // save parameters about activating or not the optimizations
        this.activateTransactionMerging = activateTransactionMerging;
        this.activateSubtreeUtilityPruning = activateSubtreeUtilityPruning;

        // record the start time
        startTimestamp = System.currentTimeMillis();

        // save minUtil value selected by the user
        this.minUtil = minUtil;

        // reset the number of itemset found
        patternCount = 0;

        // reset the memory usage checking utility
        MemoryLogger.getInstance().reset();

        // ============================
        // PHASE 1 - scan only (TWU + support + memory estimation)
        // ============================
        Phase1Stats stats = phase1ScanStats(inputPath, maximumTransactionCount);
        this.utilityBinArrayLU = stats.twu;
        this.totalItemOccurrences = stats.totalItemOccurrences;
        this.estimatedInitialDatabasePayloadBytes = totalItemOccurrences * 8L;

        List<Integer> itemsToKeep = new ArrayList<Integer>();
        for (int item = 1; item < utilityBinArrayLU.length; item++) {
            if (utilityBinArrayLU[item] >= minUtil) {
                itemsToKeep.add(item);
            } else {
                removedItemOccurrences += stats.support[item];
            }
        }
        keptItemOccurrences = totalItemOccurrences - removedItemOccurrences;
        estimatedRemovedDatabasePayloadBytes = removedItemOccurrences * 8L;
        estimatedReducedDatabasePayloadBytes = estimatedInitialDatabasePayloadBytes - estimatedRemovedDatabasePayloadBytes;
        estimatedReducedDatabasePayloadBytes+=stats.transactionCount*80;

        if(DEBUG) {
            System.out.println("===== TWU OF SINGLE ITEMS === ");
            for (int i = 1; i < utilityBinArrayLU.length; i++) {
                System.out.println("item : " + i + " twu: " + utilityBinArrayLU[i] + " support: " + stats.support[i]);
            }
            System.out.println();
        }

        // Sort promising items according to the increasing order of TWU
        insertionSort(itemsToKeep, utilityBinArrayLU);

        // Rename promising items according to the increasing order of TWU.
        oldNameToNewNames = new int[stats.maxItem + 1];
        newNamesToOldNames = new int[itemsToKeep.size() + 1];
        int currentName = 1;
        for (int j=0; j< itemsToKeep.size(); j++) {
            int item = itemsToKeep.get(j);
            oldNameToNewNames[item] = currentName;
            newNamesToOldNames[currentName] = item;
            itemsToKeep.set(j, currentName);
            currentName++;
        }

        newItemCount = itemsToKeep.size();
        utilityBinArraySU = new int[newItemCount + 1];

        // support theo new item id để estimate projected DB trước lần đệ quy đầu tiên
        renamedItemSupport = new int[newItemCount + 1];
        for (int oldItem = 1; oldItem < oldNameToNewNames.length; oldItem++) {
            int newItem = oldNameToNewNames[oldItem];
            if (newItem != 0) {
                renamedItemSupport[newItem] = stats.support[oldItem];
            }
        }


        if (DEBUG) {
            System.out.println(itemsToKeep);
            System.out.println(Arrays.toString(oldNameToNewNames));
            System.out.println(Arrays.toString(newNamesToOldNames));
            System.out.println("Estimated initial DB payload (bytes): " + estimatedInitialDatabasePayloadBytes);
            System.out.println("Estimated removed payload (bytes): " + estimatedRemovedDatabasePayloadBytes);
            System.out.println("Estimated reduced DB payload (bytes): " + estimatedReducedDatabasePayloadBytes);
        }
        System.gc();
        try {
            Thread.sleep(200);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
        usedHeapBeforeFirstRecursionAfterGc = getUsedHeapBytes();
        availableHeapBeforeFirstRecursionAfterGc = getAvailableHeapBytes();
        System.out.println(usedHeapBeforeFirstRecursionAfterGc/1024/1024);
        // ============================
        // PHASE 2 - read again and directly build reduced dataset
        // ============================
        Dataset dataset = buildReducedDataset(inputPath, maximumTransactionCount);
        averageReducedTransactionLength = calculateAverageTransactionLength(dataset);


        System.gc();
        try {
            Thread.sleep(200);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
        usedHeapBeforeFirstRecursionAfterGc = getUsedHeapBytes();
        availableHeapBeforeFirstRecursionAfterGc = getAvailableHeapBytes();
        System.out.println(usedHeapBeforeFirstRecursionAfterGc/1024/1024);


        if(DEBUG) {
            System.out.println("===== Reduced database built in phase 2 === ");

        }

        // ============================
        // PHASE 3 - same EFIM flow as before
        // ============================

        long timeStartSorting = System.currentTimeMillis();
        if(activateTransactionMerging){
            Collections.sort(dataset.getTransactions(), new Comparator<Transaction>(){
                @Override
                public int compare(Transaction t1, Transaction t2) {
                    int pos1 = t1.items.length - 1;
                    int pos2 = t2.items.length - 1;

                    if(t1.items.length < t2.items.length){
                        while(pos1 >=0){
                            int subtraction = t2.items[pos2]  - t1.items[pos1];
                            if(subtraction !=0){
                                return subtraction;
                            }
                            pos1--;
                            pos2--;
                        }
                        return -1;
                    }else if (t1.items.length > t2.items.length){
                        while(pos2 >=0){
                            int subtraction = t2.items[pos2]  - t1.items[pos1];
                            if(subtraction !=0){
                                return subtraction;
                            }
                            pos1--;
                            pos2--;
                        }
                        return 1;
                    }else{
                        while(pos2 >=0){
                            int subtraction = t2.items[pos2]  - t1.items[pos1];
                            if(subtraction !=0){
                                return subtraction;
                            }
                            pos1--;
                            pos2--;
                        }
                        return 0;
                    }
                }
            });

            int emptyTransactionCount = 0;
            for(int i=0; i< dataset.getTransactions().size();i++) {
                Transaction transaction  = dataset.getTransactions().get(i);
                if(transaction.items.length == 0){
                    emptyTransactionCount++;
                }
            }
            dataset.transactions = dataset.transactions.subList(emptyTransactionCount, dataset.transactions.size());
        }

        timeSort = System.currentTimeMillis() - timeStartSorting;

        if(DEBUG) {
            System.out.println("===== Database after transaction sorting === ");
            System.out.println(dataset.toString());
        }

        useUtilityBinArrayToCalculateSubtreeUtilityFirstTime(dataset);

        List<Integer> itemsToExplore = new ArrayList<Integer>();
        if(activateSubtreeUtilityPruning){
            for(Integer item : itemsToKeep){
                if (utilityBinArraySU[item] >= minUtil) {
                    itemsToExplore.add(item);
                }
            }
        }

        if(DEBUG) {
            System.out.println("===== List of promising items === ");
            System.out.println(itemsToKeep);
        }

        List<Integer> firstItemsToExplore = activateSubtreeUtilityPruning ? itemsToExplore : itemsToKeep;
        itemsToKeep.removeIf(e->e<itemsToExplore.get(0));
        estimateNextProjectedMemory(itemsToKeep, firstItemsToExplore,renamedItemSupport, averageReducedTransactionLength);

        System.gc();
        try {
            Thread.sleep(200);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
        usedHeapBeforeFirstRecursionAfterGc = getUsedHeapBytes();
        availableHeapBeforeFirstRecursionAfterGc = getAvailableHeapBytes();



        printCurrentNodeMemoryEstimate(itemsToKeep,itemsToExplore,renamedItemSupport,averageReducedTransactionLength,0,
                dataset.getTransactions().size());

        if(activateSubtreeUtilityPruning){
            backtrackingEFIM(dataset.getTransactions(), itemsToKeep, itemsToExplore, 0);
        }else{
            backtrackingEFIM(dataset.getTransactions(), itemsToKeep, itemsToKeep, 0);
        }

        endTimestamp = System.currentTimeMillis();

        if(writer != null) {
            writer.close();
        }

        MemoryLogger.getInstance().checkMemory();
        printPeakHeapUsage();
        return null;
    }

    /**
     * Implementation of Insertion sort for sorting a list of items by increasing order of TWU.
     * This has an average performance of O(n log n)
     * @param items list of integers to be sorted
     * @param items list the utility-bin array indicating the TWU of each item.
     */
    public static void insertionSort(List<Integer> items, int [] utilityBinArrayTWU){
        // the following lines are simply a modified an insertion sort

        for(int j=1; j< items.size(); j++){
            Integer itemJ = items.get(j);
            int i = j - 1;
            Integer itemI = items.get(i);

            // we compare the twu of items i and j
            int comparison = utilityBinArrayTWU[itemI] - utilityBinArrayTWU[itemJ];
            // if the twu is equal, we use the lexicographical order to decide whether i is greater
            // than j or not.
            if(comparison == 0){
                comparison = itemI - itemJ;
            }

            while(comparison > 0){
                items.set(i+1, itemI);

                i--;
                if(i<0){
                    break;
                }

                itemI = items.get(i);
                comparison = utilityBinArrayTWU[itemI] - utilityBinArrayTWU[itemJ];
                // if the twu is equal, we use the lexicographical order to decide whether i is greater
                // than j or not.
                if(comparison == 0){
                    comparison = itemI - itemJ;
                }
            }
            items.set(i+1,itemJ);
        }
    }

    /**
     * Recursive method to find all high-utility itemsets
     * @param transactionsOfP the list of transactions containing the current prefix P
     * @param itemsToKeep the list of secondary items in the p-projected database
     * @param itemsToExplore the list of primary items in the p-projected database
     * @param prefixLength current prefixLength
     * @throws IOException if error writing to output file
     */
    private void backtrackingEFIM( List<Transaction> transactionsOfP,
                                   List<Integer> itemsToKeep, List<Integer> itemsToExplore, int prefixLength) throws IOException {

        // update the number of candidates explored so far
        candidateCount += itemsToExplore.size();

        // ========  for each frequent item  e  =============
        for (int j = 0; j < itemsToExplore.size(); j++) {
            Integer e = itemsToExplore.get(j);
            long totalLengthPe = 0L;
            // ========== PERFORM INTERSECTION =====================
            // Calculate transactions containing P U {e}
            // At the same time project transactions to keep what appears after "e"
            List<Transaction> transactionsPe = new ArrayList<Transaction>();
            int[] supportPe = new int[newItemCount + 1];
            // variable to calculate the utility of P U {e}
            int utilityPe = 0;

            // For merging transactions, we will keep track of the last transaction read
            // and the number of identical consecutive transactions
            Transaction previousTransaction = null;
            int consecutiveMergeCount = 0;

            // this variable is to record the time for performing intersection
            long timeFirstIntersection = System.currentTimeMillis();

            // For each transaction
            for(Transaction transaction : transactionsOfP) {
                // Increase the number of transaction read
                transactionReadingCount++;

                // To record the time for performing binary searh
                long timeBinaryLocal = System.currentTimeMillis();

                // we remember the position where e appears.
                // we will call this position an "offset"
                int positionE = -1;
                // Variables low and high for binary search
                int low = transaction.offset;
                int high = transaction.items.length - 1;

                // perform binary search to find e in the transaction
                while (high >= low ) {
                    int middle = (low + high) >>> 1; // divide by 2
                    if (transaction.items[middle] < e) {
                        low = middle + 1;
                    }else if (transaction.items[middle] == e) {
                        positionE =  middle;
                        break;
                    }  else{
                        high = middle - 1;
                    }
                }
                // record the time spent for performing the binary search
                timeBinarySearch +=  System.currentTimeMillis() - timeBinaryLocal;

//	        	if(prefixLength == 0 && newNamesToOldNames[e] == 385) {
//		        	for(int i=0; i < transaction.getItems().length; i++) {
//		        		if(transaction.getItems()[i] == e) {
//		        			innerSum += transaction.getUtilities()[i];
//		        		}
//		        	}
//		        }

                // if 'e' was found in the transaction
                if (positionE > -1  ) {

                    // optimization: if the 'e' is the last one in this transaction,
                    // we don't keep the transaction
                    if(transaction.getLastPosition() == positionE){
                        // but we still update the sum of the utility of P U {e}
                        utilityPe  += transaction.utilities[positionE] + transaction.prefixUtility;
                    }else{
                        // otherwise
                        if(activateTransactionMerging && MAXIMUM_SIZE_MERGING >= (transaction.items.length - positionE)){
                            // we cut the transaction starting from position 'e'
                            Transaction projectedTransaction = new Transaction(transaction, positionE);
                            utilityPe  += projectedTransaction.prefixUtility;

                            // if it is the first transaction that we read
                            if(previousTransaction == null){
                                // we keep the transaction in memory
                                previousTransaction = projectedTransaction;
                            }else if (isEqualTo(projectedTransaction, previousTransaction)){
                                // If it is not the first transaction of the database and
                                // if the transaction is equal to the previously read transaction,
                                // we will merge the transaction with the previous one

                                // increase the number of consecutive transactions merged
                                mergeCount++;

                                // if the first consecutive merge
                                if(consecutiveMergeCount == 0){
                                    // copy items and their profit from the previous transaction
                                    int itemsCount = previousTransaction.items.length - previousTransaction.offset;
                                    int[] items = new int[itemsCount];
                                    System.arraycopy(previousTransaction.items, previousTransaction.offset, items, 0, itemsCount);
                                    int[] utilities = new int[itemsCount];
                                    System.arraycopy(previousTransaction.utilities, previousTransaction.offset, utilities, 0, itemsCount);

                                    // make the sum of utilities from the previous transaction
                                    int positionPrevious = 0;
                                    int positionProjection = projectedTransaction.offset;
                                    while(positionPrevious < itemsCount){
                                        utilities[positionPrevious] += projectedTransaction.utilities[positionProjection];
                                        positionPrevious++;
                                        positionProjection++;
                                    }

                                    // make the sum of prefix utilities
                                    int sumUtilities = previousTransaction.prefixUtility += projectedTransaction.prefixUtility;

                                    // create the new transaction replacing the two merged transactions
                                    previousTransaction = new Transaction(items, utilities, previousTransaction.transactionUtility + projectedTransaction.transactionUtility);
                                    previousTransaction.prefixUtility = sumUtilities;

                                }else{
                                    // if not the first consecutive merge

                                    // add the utilities in the projected transaction to the previously
                                    // merged transaction
                                    int positionPrevious = 0;
                                    int positionProjected = projectedTransaction.offset;
                                    int itemsCount = previousTransaction.items.length;
                                    while(positionPrevious < itemsCount){
                                        previousTransaction.utilities[positionPrevious] += projectedTransaction.utilities[positionProjected];
                                        positionPrevious++;
                                        positionProjected++;
                                    }

                                    // make also the sum of transaction utility and prefix utility
                                    previousTransaction.transactionUtility += projectedTransaction.transactionUtility;
                                    previousTransaction.prefixUtility += projectedTransaction.prefixUtility;
                                }
                                // increment the number of consecutive transaction merged
                                consecutiveMergeCount++;
                            }else{
                                // if the transaction is not equal to the preceding transaction
                                // we cannot merge it so we just add it to the database
                                transactionsPe.add(previousTransaction);
                                addSupportFromTransaction(supportPe, previousTransaction);
                                totalLengthPe += previousTransaction.items.length - previousTransaction.offset;
                                // the transaction becomes the previous transaction
                                previousTransaction = projectedTransaction;
                                // and we reset the number of consecutive transactions merged
                                consecutiveMergeCount = 0;
                            }
                        }
                    }
                    // This is an optimization for binary search:
                    // we remember the position of E so that for the next item, we will not search
                    // before "e" in the transaction since items are visited in lexicographical order
                    transaction.offset = positionE;
                }else{
                    // This is an optimization for binary search:
                    // we remember the position of E so that for the next item, we will not search
                    // before "e" in the transaction since items are visited in lexicographical order
                    transaction.offset = low;
                }
            }
            // remember the total time for peforming the database projection
            timeIntersections += (System.currentTimeMillis() - timeFirstIntersection);

            // Add the last read transaction to the database if there is one
            if(previousTransaction != null){
                transactionsPe.add(previousTransaction);
                addSupportFromTransaction(supportPe, previousTransaction);
                totalLengthPe += previousTransaction.items.length - previousTransaction.offset;
            }

            // Append item "e" to P to obtain P U {e}
            // but at the same time translate from new name of "e"  to its old name
            temp[prefixLength] = newNamesToOldNames[e];

            // if the utility of PU{e} is enough to be a high utility itemset
            if(utilityPe  >= minUtil)
            {
                // output PU{e}
                output(prefixLength, utilityPe );
            }

            //==== Next, we will calculate the Local Utility and Sub-tree utility of
            // all items that could be appended to PU{e} ====
            useUtilityBinArraysToCalculateUpperBounds(transactionsPe, j, itemsToKeep);

            // we now record time for identifying promising items
            long initialTime = System.currentTimeMillis();

            // We will create the new list of secondary items
            List<Integer> newItemsToKeep = new ArrayList<Integer>();
            // We will create the new list of primary items
            List<Integer> newItemsToExplore = new ArrayList<Integer>();

            // for each item
            for (int k = j+1; k < itemsToKeep.size(); k++) {
                Integer itemk =  itemsToKeep.get(k);

                // if the sub-tree utility is no less than min util
                if(utilityBinArraySU[itemk] >= minUtil) {
                    // and if sub-tree utility pruning is activated
                    if(activateSubtreeUtilityPruning){
                        // consider that item as a primary item
                        newItemsToExplore.add(itemk);
                    }
                    // consider that item as a secondary item
                    newItemsToKeep.add(itemk);
                }else if(utilityBinArrayLU[itemk] >= minUtil)
                {
                    // otherwise, if local utility is no less than minutil,
                    // consider this itemt to be a secondary item
                    newItemsToKeep.add(itemk);
                }
            }
            double avgLenPe = transactionsPe.isEmpty()
                    ? 0.0
                    : (double) totalLengthPe / transactionsPe.size();
            estimateNextProjectedMemory(newItemsToKeep, newItemsToExplore,supportPe, avgLenPe);
            printCurrentNodeMemoryEstimate(newItemsToKeep, newItemsToExplore, supportPe, avgLenPe, prefixLength, transactionsPe.size());

            // update the total time  for identifying promising items
            timeIdentifyPromisingItems +=  (System.currentTimeMillis() -  initialTime);

            // === recursive call to explore larger itemsets
            if(activateSubtreeUtilityPruning){
                // if sub-tree utility pruning is activated, we consider primary and secondary items
                backtrackingEFIM(transactionsPe, newItemsToKeep, newItemsToExplore,prefixLength+1);
            }else{
                // if sub-tree utility pruning is deactivated, we consider secondary items also
                // as primary items
                backtrackingEFIM(transactionsPe, newItemsToKeep, newItemsToKeep,prefixLength+1);
            }
        }

        // check the maximum memory usage for statistics purpose
        MemoryLogger.getInstance().checkMemory();
    }


    /**
     * Check if two transaction are identical
     * @param t1  the first transaction
     * @param t2  the second transaction
     * @return true if they are equal
     */
    private boolean isEqualTo(Transaction t1, Transaction t2) {
        // we first compare the transaction lenghts
        int length1 = t1.items.length - t1.offset;
        int length2 = t2.items.length - t2.offset;
        // if not same length, then transactions are not identical
        if(length1 != length2){
            return false;
        }
        // if same length, we need to compare each element position by position,
        // to see if they are the same
        int position1 = t1.offset;
        int position2 = t2.offset;

        // for each position in the first transaction
        while(position1 < t1.items.length){
            // if different from corresponding position in transaction 2
            // return false because they are not identical
            if(t1.items[position1]  != t2.items[position2]){
                return false;
            }
            // if the same, then move to next position
            position1++;
            position2++;
        }
        // if all items are identical, then return to true
        return true;
    }

    /**
     * Scan the initial database to calculate the local utility of each item
     * using a utility-bin array
     * @param dataset the transaction database
     */
    public void useUtilityBinArrayToCalculateLocalUtilityFirstTime(Dataset dataset) {

        // Initialize utility bins for all items
        utilityBinArrayLU = new int[dataset.getMaxItem() + 1];

        // Scan the database to fill the utility bins
        // For each transaction
        for (Transaction transaction : dataset.getTransactions()) {
            // for each item
            for(Integer item: transaction.getItems()) {
                // we add the transaction utility to the utility bin of the item
                utilityBinArrayLU[item] += transaction.transactionUtility;
            }
        }
    }

    /**
     * Scan the initial database to calculate the sub-tree utility of each item
     * using a utility-bin array
     * @param dataset the transaction database
     */
    public void useUtilityBinArrayToCalculateSubtreeUtilityFirstTime(Dataset dataset) {

        int sumSU;
        // Scan the database to fill the utility-bins of each item
        // For each transaction
        for (Transaction transaction : dataset.getTransactions()) {
            // We will scan the transaction backward. Thus,
            // the current sub-tree utility in that transaction is zero
            // for the last item of the transaction.
            sumSU = 0;

            // For each item when reading the transaction backward
            for(int i = transaction.getItems().length-1; i >=0; i--) {
                // get the item
                Integer item = transaction.getItems()[i];

                // we add the utility of the current item to its sub-tree utility
                sumSU += transaction.getUtilities()[i];
                // we add the current sub-tree utility to the utility-bin of the item
                utilityBinArraySU[item] += sumSU;
            }
        }
    }

    /**
     * Utilize the utility-bin arrays to calculate the sub-tree utility and local utility of all
     * items that can extend itemset P U {e}
     * @param transactionsPe the projected database for P U {e}
     * @param j the position of j in the list of promising items
     * @param itemsToKeep the list of promising items
     */
    private void useUtilityBinArraysToCalculateUpperBounds(List<Transaction> transactionsPe,
                                                           int j, List<Integer> itemsToKeep) {

        // we will record the time used by this method for statistics purpose
        long initialTime = System.currentTimeMillis();

        // For each promising item > e according to the total order
        for (int i = j + 1; i < itemsToKeep.size(); i++) {
            Integer item = itemsToKeep.get(i);
            // We reset the utility bins of that item for computing the sub-tree utility and
            // local utility
            utilityBinArraySU[item] = 0;
            utilityBinArrayLU[item] = 0;
        }

        int sumRemainingUtility;
        // for each transaction
        for (Transaction transaction : transactionsPe) {
            // count the number of transactions read
            transactionReadingCount++;

            // We reset the sum of reamining utility to 0;
            sumRemainingUtility = 0;
            // we set high to the last promising item for doing the binary search
            int high = itemsToKeep.size() - 1;

            // for each item in the transaction that is greater than i when reading the transaction backward
            // Note: >= is correct here. It should not be >.
            for (int i = transaction.getItems().length - 1; i >= transaction.offset; i--) {
                // get the item
                int item = transaction.getItems()[i];

                // We will check if this item is promising using a binary search over promising items.

                // This variable will be used as a flag to indicate that we found the item or not using the binary search
                boolean contains = false;
                // we set "low" for the binary search to the first promising item position
                int low = 0;

                // do the binary search
                while (high >= low) {
                    int middle = (low + high) >>> 1; // divide by 2
                    int itemMiddle = itemsToKeep.get(middle);
                    if (itemMiddle == item) {
                        // if we found the item, then we stop
                        contains = true;
                        break;
                    } else if (itemMiddle < item) {
                        low = middle + 1;
                    } else {
                        high = middle - 1;
                    }
                }
                // if the item is promising
                if (contains) {
                    // We add the utility of this item to the sum of remaining utility
                    sumRemainingUtility += transaction.getUtilities()[i];
                    // We update the sub-tree utility of that item in its utility-bin
                    utilityBinArraySU[item] += sumRemainingUtility + transaction.prefixUtility;
                    // We update the local utility of that item in its utility-bin
                    utilityBinArrayLU[item] += transaction.transactionUtility + transaction.prefixUtility;
                }
            }
        }
        // we update the time for database reduction for statistics purpose
        timeDatabaseReduction += (System.currentTimeMillis() - initialTime);
    }



    /**
     * Save a high-utility itemset to file or memory depending on what the user chose.
     * @param tempPosition itemset the itemset
     * @throws IOException if error while writting to output file
     */
    private void output(int tempPosition, int utility) throws IOException {
        patternCount++;
        /*
        	// if user wants to save the results to memory
		if (writer == null) {
			// we copy the temporary buffer into a new int array
			int[] copy = new int[tempPosition+1];
			System.arraycopy(temp, 0, copy, 0, tempPosition+1);
			// we create the itemset using this array and add it to the list of itemsets
			// found until now
			highUtilityItemsets.addItemset(new Itemset(copy, utility),copy.length);
		} else {
			// if user wants to save the results to file
			// create a stringuffer
			StringBuffer buffer = new StringBuffer();
			// append each item from the itemset to the stringbuffer, separated by spaces
			for (int i = 0; i <= tempPosition; i++) {
				buffer.append(temp[i]);
				if (i != tempPosition) {
					buffer.append(' ');
				}
			}
			// append the utility of the itemset
			buffer.append(" #UTIL: ");
			buffer.append(utility);

			// write the stringbuffer to file and create a new line
			// so that we are ready for writing the next itemset.
			writer.write(buffer.toString());
			writer.newLine();
		}
		*/
    }


    public static void printPeakHeapUsage()
    {
        try {
            List<MemoryPoolMXBean> pools = ManagementFactory.getMemoryPoolMXBeans();
            // we print the result in the console
            double total = 0;
            for (MemoryPoolMXBean memoryPoolMXBean : pools) {
                if (memoryPoolMXBean.getType() == MemoryType.HEAP) {
                    long peakUsed = memoryPoolMXBean.getPeakUsage().getUsed();
                    //System.out.println(String.format("Peak used for: %s is %.2f", memoryPoolMXBean.getName(), (double)peakUsed/1024/1024));
                    total = total + peakUsed;
                }
            }
            System.out.println(String.format("Total heap peak used: %f MB", total/1024/1024));

        } catch (Throwable t) {
            System.err.println("Exception in agent: " + t);
        }
    }


    private static final int BYTES_PER_ITEM_AND_UTILITY = 8;
    private static final int EXTRA_BYTES_PER_TRANSACTION = 80;

    private double calculateAverageTransactionLength(Dataset dataset) {
        if (dataset == null || dataset.getTransactions().isEmpty()) {
            return 0.0;
        }
        long totalLength = dataset.sumLength;
        return (double) totalLength / (double) dataset.getTransactions().size();
    }

    private int findPositionInItemsToKeep(List<Integer> itemsToKeep, int item) {
        for (int i = 0; i < itemsToKeep.size(); i++) {
            if (itemsToKeep.get(i) == item) {
                return i;
            }
        }
        return -1;
    }


    private double estimateAverageRemainingLengthAfterItem(double averageLength, int indexInKeep, int totalItemsToKeep) {
        if (averageLength <= 0.0 || totalItemsToKeep <= 0 || indexInKeep < 0) {
            return 0.0;
        }

        double consumedRatio = (double) (indexInKeep + 1) / (double) totalItemsToKeep;
        if (consumedRatio < 0.0) consumedRatio = 0.0;
        if (consumedRatio > 1.0) consumedRatio = 1.0;

        return Math.max(0.0, Math.ceil(averageLength * (1.0 - consumedRatio)));
    }

    private void printCurrentNodeMemoryEstimate(List<Integer> newItemsToKeep,
                                                List<Integer> newItemsToExplore,
                                                int[] supportPe,
                                                double avgLenPe,
                                                int prefixLength,
                                                int projectedTransactionCount) {
        EstimateResult nextEstimate = estimateNextProjectedMemory(
                newItemsToKeep,
                newItemsToExplore,
                supportPe,
                avgLenPe
        );

        long usedHeap = getUsedHeapBytes();
        long availableHeap = getAvailableHeapBytes();

        System.out.println("[EFIM-MEM] itemset=" + formatCurrentItemset(prefixLength)
                + " | used=" + formatMB(usedHeap)
                + " MB | free=" + formatMB(availableHeap)
                + " MB | nextNeed=" + formatMB(nextEstimate.bytes)
                + " MB | nextItem=" + nextEstimate.item
                + " | support=" + nextEstimate.support
                + " | effSupportMerge=" + nextEstimate.effectiveSupportAfterMerge
                + " | avgRemain=" + nextEstimate.avgRemainingLength
                + " | possibleSuffix=" + nextEstimate.possibleSuffixes
                + " | txPe=" + projectedTransactionCount);
    }

    private EstimateResult estimateNextProjectedMemory(List<Integer> newItemsToKeep,
                                                       List<Integer> newItemsToExplore,
                                                       int[] supportPe,
                                                       double avgLenPe) {
        EstimateResult result = new EstimateResult();

        if (newItemsToKeep == null || newItemsToKeep.isEmpty()
                || newItemsToExplore == null || newItemsToExplore.isEmpty()
                || supportPe == null) {
            return result;
        }

        List<Integer> nextItems = newItemsToExplore;

        for (Integer item : nextItems) {
            int indexInKeep = findPositionInItemsToKeep(newItemsToKeep, item);
            if (indexInKeep < 0 || item < 0 || item >= supportPe.length) {
                continue;
            }

            long support = supportPe[item];

            double avgRemainingLength = estimateAverageRemainingLengthAfterItem(
                    avgLenPe,
                    indexInKeep,
                    newItemsToKeep.size()
            );

            int remainingItemCount = newItemsToKeep.size() - indexInKeep;
            int estimatedSuffixLength = (int) Math.ceil(avgRemainingLength);
//
//
//            double possibleSuffixes = combinationAsDouble(
//                    estimatedSuffixLength,remainingItemCount
//            );
//
//            long effectiveSupportAfterMerge = (long) Math.min(
//                    support,
//                    Math.ceil(possibleSuffixes)
//            );
            long estimatedBytes = (long) Math.ceil(
                    support *
                            (avgRemainingLength * BYTES_PER_ITEM_AND_UTILITY + EXTRA_BYTES_PER_TRANSACTION)
            );

            if (estimatedBytes > result.bytes) {
                result.bytes = estimatedBytes;
                result.item = item;
                result.support = support;
                //result.effectiveSupportAfterMerge = effectiveSupportAfterMerge;
                result.avgRemainingLength = avgRemainingLength;
                //result.possibleSuffixes = possibleSuffixes;
            }
        }

        estimatedRecursiveEstimateCount++;

        if (result.bytes > estimatedRecursiveMemoryBytesMax) {
            estimatedRecursiveMemoryBytesMax = result.bytes;
            estimatedRecursiveMaxItem = result.item;
            estimatedRecursiveMaxDepth = -1;
            estimatedRecursiveMaxSupport = result.support;
            estimatedRecursiveMaxAvgRemainingLength = result.avgRemainingLength;
        }

        return result;
    }

    private static final class EstimateResult {
        long bytes = 0L;
        int item = -1;
        long support = 0L;
        double avgRemainingLength = 0.0;

        long effectiveSupportAfterMerge = 0L;
        double possibleSuffixes = 0.0;
    }

    private String formatCurrentItemset(int prefixLength) {
        StringBuilder builder = new StringBuilder();
        builder.append('[');
        for (int i = 0; i <= prefixLength; i++) {
            if (i > 0) {
                builder.append(' ');
            }
            builder.append(oldNameToNewNames[temp[i]]);
        }
        builder.append(']');
        return builder.toString();
    }

    private String formatItem(int newItem) {
        if (newItem <= 0 || newNamesToOldNames == null || newItem >= newNamesToOldNames.length) {
            return "-";
        }
        return String.valueOf(newNamesToOldNames[newItem]);
    }

    private String formatMB(long bytes) {
        return String.format("%.2f", bytes / 1024.0 / 1024.0);
    }

//    private void estimateFirstRecursionMemory(List<Integer> itemsToKeep, List<Integer> itemsToExplore) {
//        estimatedFirstRecursionMemoryBytesMax = 0L;
//        estimatedFirstRecursionSupportMin = Long.MAX_VALUE;
//        estimatedFirstRecursionSupportMax = 0L;
//        estimatedFirstRecursionMaxItem = -1;
//        estimatedFirstRecursionMaxAvgRemainingLength = 0.0;
//
//        if (itemsToKeep == null || itemsToKeep.isEmpty() || itemsToExplore == null || itemsToExplore.isEmpty()) {
//            return;
//        }
//        int itemtoKeepsize = itemsToKeep.size();
//        for (Integer item : itemsToKeep){
//            if(item<itemsToExplore.get(0)){
//                itemtoKeepsize--;
//            }
//            if(item==itemsToExplore.get(0)){
//                break;
//            }
//        }
//
//        for (Integer item : itemsToExplore) {
//            int indexInKeep = findPositionInItemsToKeep(itemsToKeep, item);
//            if (indexInKeep < 0) {
//                continue;
//            }
//
//            long support = renamedItemSupport[item];
//            double avgRemainingLength = estimateAverageRemainingLengthAfterItem(averageReducedTransactionLength,indexInKeep, itemtoKeepsize);
//            long estimatedBytes = (long) Math.ceil(
//                    support * (avgRemainingLength * BYTES_PER_ITEM_AND_UTILITY + EXTRA_BYTES_PER_TRANSACTION)
//            );
//
//
//            if (estimatedBytes > estimatedFirstRecursionMemoryBytesMax) {
//                estimatedFirstRecursionMemoryBytesMax = estimatedBytes;
//                estimatedFirstRecursionMaxItem = item;
//                estimatedFirstRecursionMaxAvgRemainingLength = avgRemainingLength;
//            }
//            if (support < estimatedFirstRecursionSupportMin) {
//                estimatedFirstRecursionSupportMin = support;
//            }
//            if (support > estimatedFirstRecursionSupportMax) {
//                estimatedFirstRecursionSupportMax = support;
//            }
//
//            if (DEBUG) {
//                System.out.println("[FIRST-EST] item=" + newNamesToOldNames[item]
//                        + " indexInKeep=" + indexInKeep
//                        + " support=" + support
//                        + " avgRemainingLen=" + avgRemainingLength
//                        + " memEstMB=" + (estimatedBytes / 1024.0 / 1024.0));
//            }
//        }
//    }

    public static long getUsedHeapBytes() {
        Runtime rt = Runtime.getRuntime();
        return rt.totalMemory() - rt.freeMemory();
    }

    public static long getAvailableHeapBytes() {
        Runtime rt = Runtime.getRuntime();
        long used = rt.totalMemory() - rt.freeMemory();
        return rt.maxMemory() - used;
    }


    /**
     * Print statistics about the latest execution of the EFIM algorithm.
     */
    public void printStats() {

        System.out.println("========== EFIM STATS ==========");
        System.out.println(" minUtil: " + minUtil);
        System.out.println(" High utility itemsets count: " + patternCount);
        System.out.println(" Total time: " + (endTimestamp - startTimestamp) + " ms");
        System.out.println(" Max memory: " + MemoryLogger.getInstance().getMaxMemory() + " MB");
        System.out.println(" Candidate count: " + candidateCount);
        System.out.println("================================");
    }

    private void addSupportFromTransaction(int[] supportPe, Transaction transaction) {
        for (int p = transaction.offset; p < transaction.items.length; p++) {
            supportPe[transaction.items[p]]++;
        }
    }
    private double combinationAsDouble(int n, int k) {
        if (k < 0 || k > n) return 0.0;
        if (k == 0 || k == n) return 1.0;

        k = Math.min(k, n - k);

        double result = 1.0;
        for (int i = 1; i <= k; i++) {
            result = result * (n - k + i) / i;

            if (result > Long.MAX_VALUE) {
                return Long.MAX_VALUE;
            }
        }

        return result;
    }
}
