/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package alp;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.logging.Level;
import java.util.logging.Logger;
import javafx.stage.FileChooser;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import javax.swing.Timer;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableModel;
import org.chocosolver.solver.search.loop.monitors.IMonitorSolution;
import org.chocosolver.solver.search.solution.Solution;

/**
 *
 * @author Yasser
 */
public class ALP_GUI extends javax.swing.JFrame implements IMonitorSolution {
    
    /**
     * Creates new form ALP_GUI
     */
    Timer timer=null;
    ALP alp=null;
    public static ALP_GUI gui=null;
    int lastSolution=-1;
    public ALP_GUI() {
        initComponents();
        String filename="/testdata/"+(String)comboFile.getSelectedItem();
        int [][] data=DataFetch.parse(DataFetch.getDataFromResource(filename));
        updateTables(data);
    }

    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        comboFile = new javax.swing.JComboBox();
        spinRunWay = new javax.swing.JSpinner();
        jLabel1 = new javax.swing.JLabel();
        btnExecute = new javax.swing.JButton();
        jScrollPane1 = new javax.swing.JScrollPane();
        tableAirplanes = new javax.swing.JTable();
        jScrollPane2 = new javax.swing.JScrollPane();
        tablesSeparation = new javax.swing.JTable();
        jScrollPane3 = new javax.swing.JScrollPane();
        tableSolution = new javax.swing.JTable();
        jScrollPane4 = new javax.swing.JScrollPane();
        txtInfo = new javax.swing.JTextArea();
        jLabel2 = new javax.swing.JLabel();
        jLabel3 = new javax.swing.JLabel();
        jLabel4 = new javax.swing.JLabel();
        labelSolutionCost = new javax.swing.JLabel();
        btnStopExecution = new javax.swing.JButton();

        setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);

        comboFile.setModel(new javax.swing.DefaultComboBoxModel(new String[] { "airland1.txt", "airland2.txt", "airland3.txt", "airland4.txt", "airland5.txt", "airland6.txt", "airland7.txt", "airland8.txt", "airland9.txt", "airland10.txt", "airland11.txt", "airland12.txt", "airland13.txt", "choose a custom file" }));
        comboFile.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                comboFileActionPerformed(evt);
            }
        });

        spinRunWay.setModel(new javax.swing.SpinnerNumberModel(1, 1, 4, 1));

        jLabel1.setText("Run Ways");

        btnExecute.setText("Find Best Solution");
        btnExecute.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                btnExecuteActionPerformed(evt);
            }
        });

        tableAirplanes.setModel(new javax.swing.table.DefaultTableModel(
            new Object [][] {

            },
            new String [] {

            }
        ));
        jScrollPane1.setViewportView(tableAirplanes);

        tablesSeparation.setModel(new javax.swing.table.DefaultTableModel(
            new Object [][] {
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null}
            },
            new String [] {
                "Title 1", "Title 2", "Title 3", "Title 4"
            }
        ));
        jScrollPane2.setViewportView(tablesSeparation);

        tableSolution.setModel(new javax.swing.table.DefaultTableModel(
            new Object [][] {
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null}
            },
            new String [] {
                "Title 1", "Title 2", "Title 3", "Title 4"
            }
        ));
        jScrollPane3.setViewportView(tableSolution);

        txtInfo.setColumns(20);
        txtInfo.setRows(5);
        jScrollPane4.setViewportView(txtInfo);

        jLabel2.setText("Airplanes Information");

        jLabel3.setText("Separation Data");

        jLabel4.setText("Best Solution Found");

        labelSolutionCost.setText("Solution");

        btnStopExecution.setText("Stop Execution");
        btnStopExecution.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                btnStopExecutionActionPerformed(evt);
            }
        });

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
        getContentPane().setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(jScrollPane3)
                    .addComponent(jScrollPane2)
                    .addGroup(layout.createSequentialGroup()
                        .addComponent(comboFile, javax.swing.GroupLayout.PREFERRED_SIZE, 137, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addGap(63, 63, 63)
                        .addComponent(jLabel1)
                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                        .addComponent(spinRunWay, javax.swing.GroupLayout.PREFERRED_SIZE, 74, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, 53, Short.MAX_VALUE)
                        .addComponent(btnStopExecution, javax.swing.GroupLayout.PREFERRED_SIZE, 133, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                        .addComponent(btnExecute, javax.swing.GroupLayout.PREFERRED_SIZE, 151, javax.swing.GroupLayout.PREFERRED_SIZE))
                    .addComponent(jScrollPane1)
                    .addComponent(jScrollPane4)
                    .addGroup(layout.createSequentialGroup()
                        .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                            .addComponent(jLabel2, javax.swing.GroupLayout.PREFERRED_SIZE, 151, javax.swing.GroupLayout.PREFERRED_SIZE)
                            .addComponent(jLabel3, javax.swing.GroupLayout.PREFERRED_SIZE, 138, javax.swing.GroupLayout.PREFERRED_SIZE)
                            .addGroup(layout.createSequentialGroup()
                                .addComponent(jLabel4, javax.swing.GroupLayout.PREFERRED_SIZE, 123, javax.swing.GroupLayout.PREFERRED_SIZE)
                                .addGap(18, 18, 18)
                                .addComponent(labelSolutionCost, javax.swing.GroupLayout.PREFERRED_SIZE, 93, javax.swing.GroupLayout.PREFERRED_SIZE)))
                        .addGap(0, 0, Short.MAX_VALUE)))
                .addContainerGap())
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(comboFile, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(spinRunWay, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(jLabel1)
                    .addComponent(btnExecute)
                    .addComponent(btnStopExecution))
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(jLabel2)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(jScrollPane1, javax.swing.GroupLayout.PREFERRED_SIZE, 132, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(jLabel3)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(jScrollPane2, javax.swing.GroupLayout.PREFERRED_SIZE, 113, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(jLabel4)
                    .addComponent(labelSolutionCost))
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(jScrollPane3, javax.swing.GroupLayout.PREFERRED_SIZE, 57, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(jScrollPane4, javax.swing.GroupLayout.PREFERRED_SIZE, 140, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addGap(0, 0, Short.MAX_VALUE))
        );

        pack();
    }// </editor-fold>//GEN-END:initComponents

    private void btnExecuteActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_btnExecuteActionPerformed
        if(!ALP.exectuting){
            String filename=null;
            String[] args={};
            int runways=((Integer)spinRunWay.getModel().getValue()).intValue();
            if(comboFile.getSelectedIndex()==13){ //choose a file
                JFileChooser choose=new JFileChooser();
                int code=choose.showOpenDialog(this);
                if(code==JFileChooser.OPEN_DIALOG){
                    filename=choose.getSelectedFile().getAbsolutePath();
                    //update file data
                    alp=new ALP(DataFetch.getDataFromFile(filename),runways);  
                }
            }
            else{
                filename="/testdata/"+(String)comboFile.getSelectedItem();
                alp=new ALP(DataFetch.getDataFromResource(filename),runways);  
            }
            gui=this;
            Thread t=new Thread(){  
                   public void run(){
                            alp.solveProblem(gui,args);
                        }
                    };
            ALP.exectuting=true;
            t.start();

            //create a timer to update GUI with the solution
            //create  thread to update the GUI
            int delay = 500; //milliseconds
            ActionListener taskPerformer = new ActionListener() {
                public void actionPerformed(ActionEvent evt) {
                        DefaultTableModel model=new DefaultTableModel();
                        model.addColumn(" ");
                        for(int i=0;i<ALP.n;i++){
                            model.addColumn("Plane"+i);
                        }

                         Object[] row=new Object[ALP.n+1];
                         Solution s=ALP.solver.getSolutionRecorder().getLastSolution();
                         
                         if(s==null)
                             return;
                         int currentSolution=s.getIntVal(ALP.objective);
                         if(lastSolution!=currentSolution){
                             lastSolution=currentSolution;
                            row[0]="Landing Time";
                            for(int j=0;j<ALP.n;j++){
                                row[j+1]=s.getIntVal(ALP.planes_landing_time[j]);
                            }
                            model.addRow(row);
                            tableSolution.setModel(model);
                         }
                }
            };
            timer=new Timer(delay, taskPerformer);
            timer.start();
        }
        else
            JOptionPane.showMessageDialog(this,"Still Executing, wait tell finishing");
    }//GEN-LAST:event_btnExecuteActionPerformed

    private void comboFileActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_comboFileActionPerformed
        String filename="/testdata/"+(String)comboFile.getSelectedItem();
        int [][] data=DataFetch.parse(DataFetch.getDataFromResource(filename));
        updateTables(data);
    }//GEN-LAST:event_comboFileActionPerformed

    private void btnStopExecutionActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_btnStopExecutionActionPerformed
        if(ALP.exectuting){
            ALP.solver.unplugAllMonitors();
            ALP.exectuting=false;
            if(timer!=null)
                timer.stop();
                StopCriteria.stopSearch=true;
                lastSolution=-1;
        }
        
    }//GEN-LAST:event_btnStopExecutionActionPerformed
    
    private void updateTables(int[][] data){
        DefaultTableModel model=new DefaultTableModel();
        DefaultTableModel modelSeparation=new DefaultTableModel();
        
       int planesCount=data.length;
       model.addColumn("Column Information");
       modelSeparation.addColumn(" ");
       for(int i=0;i<planesCount;i++){
           model.addColumn("Plane"+i);
           modelSeparation.addColumn("Plane"+i);
       }
       for(int i=0;i<6;i++){ //each plane data
           Object[] row=new Object[planesCount+1];
           switch(i){
               case 0:           
                   row[0]="Appearance";
                   break;
               case 1:
                   row[0]="Ei";
                   break;
               case 2:
                   row[0]="Ti";
                   break;
               case 3:
                   row[0]="Li";
                   break;
               case 4:
                   row[0]="Penalty Cost Before";
                   break;
               case 5:
                   row[0]="Penalty Cost After";
                   break;
           }
           for(int j=0;j<planesCount;j++){
               row[j+1]=data[j][i];
           }
           model.addRow(row);
       }
       for(int i=0;i<planesCount;i++){
           Object[] row=new Object[planesCount+1];
           row[0]="plane"+i;
           for(int j=0;j<planesCount;j++){
               row[j+1]=data[i][6+j];               
           }
           modelSeparation.addRow(row);
       }
       tableAirplanes.setModel(model);
       tablesSeparation.setModel(modelSeparation);
    }
    /**
     * @param args the command line arguments
     */
    public static void main(String args[]) {
        /* Set the Nimbus look and feel */
        //<editor-fold defaultstate="collapsed" desc=" Look and feel setting code (optional) ">
        /* If Nimbus (introduced in Java SE 6) is not available, stay with the default look and feel.
         * For details see http://download.oracle.com/javase/tutorial/uiswing/lookandfeel/plaf.html 
         */
        try {
            for (javax.swing.UIManager.LookAndFeelInfo info : javax.swing.UIManager.getInstalledLookAndFeels()) {
                if ("Nimbus".equals(info.getName())) {
                    javax.swing.UIManager.setLookAndFeel(info.getClassName());
                    break;
                }
            }
        } catch (ClassNotFoundException ex) {
            java.util.logging.Logger.getLogger(ALP_GUI.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (InstantiationException ex) {
            java.util.logging.Logger.getLogger(ALP_GUI.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (IllegalAccessException ex) {
            java.util.logging.Logger.getLogger(ALP_GUI.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (javax.swing.UnsupportedLookAndFeelException ex) {
            java.util.logging.Logger.getLogger(ALP_GUI.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        }
        //</editor-fold>

        /* Create and display the form */
        java.awt.EventQueue.invokeLater(new Runnable() {
            public void run() {
                new ALP_GUI().setVisible(true);
            }
        });
    }

    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JButton btnExecute;
    private javax.swing.JButton btnStopExecution;
    private javax.swing.JComboBox comboFile;
    private javax.swing.JLabel jLabel1;
    private javax.swing.JLabel jLabel2;
    private javax.swing.JLabel jLabel3;
    private javax.swing.JLabel jLabel4;
    private javax.swing.JScrollPane jScrollPane1;
    private javax.swing.JScrollPane jScrollPane2;
    private javax.swing.JScrollPane jScrollPane3;
    private javax.swing.JScrollPane jScrollPane4;
    private javax.swing.JLabel labelSolutionCost;
    private javax.swing.JSpinner spinRunWay;
    private javax.swing.JTable tableAirplanes;
    private javax.swing.JTable tableSolution;
    private javax.swing.JTable tablesSeparation;
    private javax.swing.JTextArea txtInfo;
    // End of variables declaration//GEN-END:variables

    @Override
    public void onSolution() {
        int s=ALP.solver.getSolutionRecorder().getLastSolution().getIntVal(ALP.objective);
        labelSolutionCost.setText(":"+s);
        txtInfo.setText(ALP.solver.getMeasures().toString());
    }
}
