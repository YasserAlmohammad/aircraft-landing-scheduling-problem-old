/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package alp;

import org.chocosolver.util.criteria.Criterion;

/**
 *
 * @author Yasser
 */
public class StopCriteria implements Criterion {
    
    public static boolean stopSearch=false;
    @Override
    public boolean isMet() {
        return stopSearch;
    }
    
}
