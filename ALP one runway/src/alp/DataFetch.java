/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package alp;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.InputStreamReader;
import java.util.Scanner;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.Pattern;

/**
 *passing a file name, read the file content and store it into a String
 *The format of these data files is:
 *number of planes (p), freeze time
 *for each plane i (i=1,...,p):
 *  appearance time, earliest landing time, target landing time,
 *  latest landing time, penalty cost per unit of time for landing
 *  before target, penalty cost per unit of time for landing
 *  after target
 *  for each plane j (j=1,...p): separation time required after 
 *                               i lands before j can land
 */
public class DataFetch {
        private static final String groupSeparator = "\\,";
        private static final String decimalSeparator = "\\.";
        private static final String non0Digit = "[\\p{javaDigit}&&[^0]]";
        private static Pattern decimalPattern;
        static {
        // \\p{javaDigit} may not be perfect, see above
        String digit = "([0-9])";
        String groupedNumeral = "(" + non0Digit + digit + "?" + digit + "?(" +
                groupSeparator + digit + digit + digit + ")+)";
        String numeral = "((" + digit + "++)|" + groupedNumeral + ")";
        String decimalNumeral = "(" + numeral + "|" + numeral +
                decimalSeparator + digit + "*+|" + decimalSeparator +
                digit + "++)";
        decimalPattern = Pattern.compile("([-+]?" + decimalNumeral + ")");
    }
        
        public static int[][] parse(String source) {
            int[][] data;
            Scanner sc = new Scanner(source);
            int nb = sc.nextInt();
            data = new int[nb][6 + nb];
            int freeze=sc.nextInt();
            for (int i = 0; i < nb; i++) {
                data[i][0] = sc.nextInt(); // appearance time
                data[i][1] = sc.nextInt(); // earliest landing time
                data[i][2] = sc.nextInt(); // target landing time
                data[i][3] = sc.nextInt(); // latest landing time
                Double tt = Double.parseDouble(sc.next(decimalPattern));
                data[i][4] = (int) Math.ceil(tt); // penalty cost per unit of time for landing before target
                tt = Double.parseDouble(sc.next(decimalPattern));
                data[i][5] = (int) Math.ceil(tt); // penalty cost per unit of time for landing after target
                for (int j = 0; j < nb; j++) {
                    data[i][6 + j] = sc.nextInt();
                }
        }
        sc.close();
        return data;
    }
        
    /**
     * for custom files to be loaded from the file system
     * @param filename  absolute file name
     * @return 
     */
    public static String getDataFromFile(String filename){
        StringBuilder builder=new StringBuilder();
        BufferedReader reader;
        try {
            reader=new BufferedReader(new FileReader(filename));
            String line=null;
            while((line=reader.readLine())!=null){
                builder.append(line);
            }
        } catch (Exception ex) {
            System.out.println("error reading datafile");
        }
        return builder.toString();
    }
    
    /**
     * to load a test sample from the package (airland1.txt ... 13.txt) packed with the project.
     * @param resourcename
     * @return 
     */
    public static String getDataFromResource(String resourcename){
        StringBuilder builder=new StringBuilder();
        BufferedReader reader;
        try {
            reader=new BufferedReader(new InputStreamReader(DataFetch.class.getResourceAsStream(resourcename)));
            String line=null;
            while((line=reader.readLine())!=null){
                builder.append(line);
            }
        } catch (Exception ex) {
            System.out.println("error reading datafile");
        }
        return builder.toString();
    }
}
