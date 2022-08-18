import java.io.*;
import java.util.*;
public class Main {
    static int n;
    static int a;
    static int noOfInst;
    static String[][] programs;
    static Node[][] graph;
    static boolean[][] vis;
    static int[] idx;
    static Node root;
    static String cond;
    static HashMap<String, ArrayList<String>> rfmap;
    static HashMap<String, ArrayList<String>> wsmap;
    static HashMap<String, Node> tracemap;
    static boolean assertres = true;
    static ArrayList<Solution> answer;
    static StringBuilder rfTraces = new StringBuilder("") , wsTraces = new StringBuilder("");
    static Node xzero = new Node() , yzero = new Node() , zzero = new Node();

    public static int getTraceLength(Node root ){
        int len = 0;
        while(root!=null){
            len++;
            root = root.next;
        }
        return len;
    }

    public static String[] assignProperties(Node root , int index){
        String[] properties = {root.LHS.trim() , root.RHS.trim() , (root.clock+"").trim() , (root.read == true ? "read" : "write").trim()};
        return properties;
    }
    

    public static String printRF(Node root){
        
        ArrayList<String> rflist = new ArrayList<>();
        StringBuffer rfstr = new StringBuffer("");
        
        rfTraces = new StringBuilder();
        while(root!=null){
            if(root.rf != null && root.clock >= 3 ){
                for(int i = 0 ;i < root.rfindex;i++) {
                    rfTraces.append("["+root.LHS+"="+root.RHS+" , "+root.rf[i].LHS+"="+root.rf[i].RHS+"], ");
                   
                    rflist.add(root.LHS+"="+root.RHS+" "+root.programNum+" "+root.instrcutionNumber+","+root.rf[i].LHS+"="+root.rf[i].RHS+" "+root.rf[i].programNum+" "+root.rf[i].instrcutionNumber);
                }
            }
            root = root.next;
        }
        
        Collections.sort(rflist);
        for (String i : rflist) {
            rfstr.append(i + " ");
        }
        if (!rfmap.containsKey(rfstr.toString())) {
            rfmap.put(rfstr.toString(), rflist);
        }
        return rfstr.toString();
    }

    
    public static String printWS(Node root){
        
        ArrayList<String> wslist = new ArrayList<>();
        StringBuffer wsstr = new StringBuffer("");
        wsTraces  = new StringBuilder();
        while(root!=null){
           
            if(root.ws != null   ){
                for(int i = 0 ;i < root.wsindex;i++) {
                    if(root.clock >= 3)
                    wsTraces.append("[ "+root.LHS+"="+root.RHS+" , "+root.ws[i].LHS+"="+root.ws[i].RHS+"], ");
                    
                    wslist.add(root.LHS+"="+root.RHS+" "+root.programNum+" "+root.instrcutionNumber+","+root.ws[i].LHS+"="+root.ws[i].RHS+" "+root.ws[i].programNum+" "+root.ws[i].instrcutionNumber);
                }
            }
            root = root.next;
        }
        
        Collections.sort(wslist);
        for (String i : wslist) {
            wsstr.append(i + " ");
        }
        if (!wsmap.containsKey(wsstr.toString())) {
            wsmap.put(wsstr.toString(), wslist);
        }
        return wsstr.toString();
    }

    // public static void printFR(Node root){
        
    //     while(root!=null){
    //         if(root.fr != null){
    //             for(int i = 0 ;i < root.frindex;i++)
    //                 System.out.println(root.LHS+"="+root.RHS+"------>"+root.fr[i].LHS+"="+root.fr[i].RHS);
    //         }
    //         root = root.next;
    //     }
    //     System.out.println("-------------------------");
    // }

    
    

   

    public static Node clone(Node root){
        Node temp = root;
        int len = getTraceLength(temp);
        Node ptr = new Node();
        Node head = ptr;
        temp = root;
        while(len-- > 0){
            Node ptr1 = new Node();
            ptr1.var = temp.var;
            ptr1.LHS = temp.LHS;
            ptr1.RHS = temp.RHS;
            ptr1.read = temp.read;
            ptr1.write = temp.write;
            ptr1.clock = temp.clock;
            ptr1.programNum = temp.programNum;
            ptr1.instrcutionNumber = temp.instrcutionNumber;
            ptr.next = ptr1;
            ptr = ptr.next;
            temp = temp.next;
        }
        head = head.next;
       
        return head;
    }

    public static boolean hasCycle(Node root , boolean[] visited){

        if(root == null || root.clock == 0) return false;
        if(visited[root.clock] == true)
        return true;

        visited[root.clock] = false;
        boolean flag = false;

        flag  = flag || hasCycle(root.next , visited);
        if(flag == true)
        return true;

        for(int j = 0;j < root.rfindex;j++){
            flag = flag || hasCycle(root.rf[j], visited);
            if(flag == true)
            return true;
        }

        
        for(int j = 0;j < root.frindex;j++){
            flag = flag || hasCycle(root.fr[j], visited);
            if(flag == true)
            return true;
        }

        
        for(int j = 0;j < root.wsindex;j++){
            flag = flag || hasCycle(root.ws[j], visited);
            if(flag == true)
            return true;
        }
       

        return false;

    }

    public static boolean isCyclic(Node root){
        Node temp = root;
        int numOfNodes = getTraceLength(temp);
        boolean[] visited = new boolean[numOfNodes];
        temp = root;
        boolean flag = false;
        for(int i = 0;i < numOfNodes;i++){

            visited[temp.clock] = true;

            flag  = flag || hasCycle(temp.next , visited);
            if(flag == true)
            return true;

            for(int j = 0;j < temp.rfindex;j++){
                flag = flag || hasCycle(temp.rf[j], visited);
                if(flag == true)
                return true;
            }

            
            for(int j = 0;j < temp.frindex;j++){
                flag = flag || hasCycle(temp.fr[j], visited);
                if(flag == true)
                return true;
            }

            
            for(int j = 0;j < temp.wsindex;j++){
                flag = flag || hasCycle(temp.ws[j], visited);
                if(flag == true)
                return true;
            }

            visited[temp.clock] = false;
            temp = temp.next;

        }
        return false;
    }

    public static boolean detectCycle(Node newroot) {
        
        /*
        in properties array
        0 index stores LHS of instructions
        1 index stores RHS of instructions
        2 index stores clock value of instructions (used in hashmap to match nodes)
        3 index stores type of instruction (read/write) (used for matching read---write and write---read)
        */
        
        Node root = clone(newroot);
        Node temp = root;
        int lenOfTrace = getTraceLength(temp);
        HashMap  <Integer,Node> map = new HashMap<>();
        String[][] properties = new String[lenOfTrace][4];
        int index = 0;
        temp = root;
        StringBuilder trace = new StringBuilder(" [");
        while(temp != null){
            map.put(temp.clock , temp);
            if(temp.next == null && temp.clock >= 3)
                trace.append(temp.LHS+"="+temp.RHS+" ");

            else if(temp.next != null && temp.clock >= 3)
                trace.append(temp.LHS+"="+temp.RHS+" , ");
            properties[index] = assignProperties(temp , index);
            index++;
            temp = temp.next;
        }
        trace.append("] ,");
       

        for(int i = 1;i < lenOfTrace;i++){
            for(int j = i - 1;j >= 0 ;j--){
               
                if( (properties[i][3]).equals("read") && (properties[j][3]).equals("write") && (properties[i][1]).equals(properties[j][0]) ){
                    
                    Node writeNode = map.get(Integer.parseInt(properties[j][2])) , readNode = map.get(Integer.parseInt(properties[i][2]));
                    
                    writeNode.rf[writeNode.rfindex++] = readNode;
                    break;
                }
              
                else if( (properties[i][3]).equals("write") && (properties[j][3]).equals("write") && (properties[i][0]).equals(properties[j][0])){
                    
                    
                    
                    Node fromwWriteNode = map.get(Integer.parseInt(properties[j][2])) , toWriteNode = map.get(Integer.parseInt(properties[i][2]));
                    fromwWriteNode.ws[fromwWriteNode.wsindex++] = toWriteNode;
                   
                    break;
                }

                
            }
        }

        for(int i = 0;i < lenOfTrace;i++){
           
            if( (properties[i][3]).equals("write"))continue;
            for(int j = i + 1;j < lenOfTrace;j++){
            
                if( (properties[j][3]).equals("write") && (properties[i][1]).equals(properties[j][0])  ){
                    Node readNode = map.get(Integer.parseInt(properties[i][2])) , writeNode = map.get(Integer.parseInt(properties[j][2]));
                    readNode.fr[readNode.frindex++] = writeNode;
                }

            }
        }

        temp = root;
        String rfstr = printRF(temp);
        
      
        temp = root;
        String wsstr = printWS(temp);
        
       
        
        String traceKey = rfstr + wsstr;

        if(traceKey.length() != 0 && !tracemap.containsKey(traceKey)){
            Solution obj = new Solution();
            obj.trace = trace.toString();
            obj.rf = rfTraces.toString();
            obj.ws = wsTraces.toString();
            answer.add(obj);
            tracemap.put(traceKey, temp); 
            
        }
     
        
        return isCyclic(temp);
    }


    static int instrcutionNumber = 0;
    public static void constructGraph(int r, int clock) {
        if(assertres == false) return;

        if (clock == noOfInst - 1 + 3) {
            // detect cycles
            Node curr = graph[r][idx[r]];
            curr.clock = clock;
            instrcutionNumber++;
         
            Node temp1 = root;
            if(a == 1)
                assertres  = assertCheck(temp1);
            boolean res = detectCycle(root);
            
            if(assertres == false){
                System.out.println("Error: Assertion Violation");
                Node temp = root;
                
                System.out.print("Violating Trace:");
                System.out.print("[ ");

                while(temp!=null){
                   if(!temp.isSpecialNode)   
                    System.out.print(temp.LHS+"="+temp.RHS+" ; ");
                    temp = temp.next;
                }
                System.out.print("], ");
                // System.out.println();
                System.out.print("rf relation:[");
                System.out.print(rfTraces.substring(0,rfTraces.length()-2));
                System.out.print("], ");
                System.out.print("co relation:[");
                System.out.print(wsTraces.substring(0,wsTraces.length()-2));
                System.out.print("] ");
                System.out.println();
            }
            curr = null;
            return;
        }
        vis[r][idx[r]] = true;
        Node curr = graph[r][idx[r]];
        idx[r]++;
        curr.clock = clock;
        for (int i = 0; i < n; i++) {
            if (idx[i] < vis[i].length && !vis[i][idx[i]]) {
                curr.next = graph[i][idx[i]];
                constructGraph(i, clock + 1);
                curr.next = null;
                
            }
        }
        idx[r]--;
        vis[r][idx[r]] = false;
    }

    public static void main(String[] args) throws IOException {
        BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
        // ---------- Input ------------------------
        n = Integer.parseInt(reader.readLine().trim());
        programs = new String[n][];
        for (int i = 0; i < n; i++) {
            programs[i] = reader.readLine().trim().split(";");
        }
        a = Integer.parseInt(reader.readLine().trim());
        if (a == 1) {
            cond = (reader.readLine().trim().split("assert")[1]);//------------------------
            StringBuilder sb = new StringBuilder("");
            for(int i = 1;i < cond.length()-1;i++)
            sb.append(cond.charAt(i));
            cond = sb.toString();
            // System.out.println("cond  "+cond);
        }
        // ---------- Input End ------------------------

        // ---------- Construct Graph ------------------------
        // 1. Make PO edges
        graph = new Node[n][];
        vis = new boolean[n][];
        rfmap = new HashMap<>();
        wsmap = new HashMap<>();
        tracemap = new HashMap<>();

        answer = new ArrayList<Solution>();

        for (int i = 0; i < n; i++) {
            graph[i] = new Node[programs[i].length];
            vis[i] = new boolean[programs[i].length];
            noOfInst += programs[i].length;
            for (int j = 0; j < programs[i].length; j++) {
                graph[i][j] = new Node();
                graph[i][j].programNum = i+1;
                graph[i][j].instrcutionNumber = j;
                String[] str = programs[i][j].split("=");
                boolean isNumeric = str[1].chars().allMatch( Character::isDigit );
                if (isNumeric) {
                    graph[i][j].write = true;
                    graph[i][j].var = str[0];
                    graph[i][j].LHS = str[0];
                    graph[i][j].RHS = str[1];


                } else {
                    graph[i][j].read = true;
                    graph[i][j].var = str[1];
                    graph[i][j].LHS = str[0];
                    graph[i][j].RHS = str[1];


                }
            }

            for(int j = 0;j < programs[i].length;j++){
                if (j < programs[i].length - 1)
                graph[i][j].po = graph[i][j + 1];
            }
        }
        // 2. Make rf and fr edges

        // Need to make index map?
        idx = new int[n];
        for (int i = 0; i < n; i++) {

            
            xzero.next = yzero;
            yzero.next = zzero;
            zzero.next = graph[i][0];

            xzero.LHS = "x";
            xzero.RHS = "0";
            xzero.isSpecialNode = true;
            xzero.clock = 0;
            xzero.programNum = 0;
            xzero.instrcutionNumber = 1;


            yzero.LHS = "y";
            yzero.RHS = "0";
            yzero.isSpecialNode = true;
            yzero.clock = 1;
            yzero.programNum = 0;
            yzero.instrcutionNumber = 2;

            zzero.LHS = "z";
            zzero.RHS = "0";
            zzero.isSpecialNode = true;
            zzero.clock = 2;
            zzero.programNum = 0;
            zzero.instrcutionNumber = 3;

            root = xzero;  //initially root = graph[i][0];
            
            constructGraph(i, 3);
        }
        long ele = 1;
        if(assertres == true){
            System.out.println("No. of traces = "+answer.size());
            for(Solution ob : answer){
                System.out.print(ele+"-:");
                ele++;
                System.out.print("Trace: ");
                System.out.print(ob.trace);
                System.out.print("rf relation");
                System.out.print("[");
                if(ob.rf.length() >= 2)
                System.out.print(ob.rf.substring(0,ob.rf.length()-2));
                System.out.print("], ");
                System.out.print("co relation");
                System.out.print("[");
                if(ob.ws.length() >= 2)
                System.out.print(ob.ws.substring(0,ob.ws.length()-2));
                System.out.print("] ");
                System.out.println();
            }
        }

        // ---------- End ------------------------

        reader.close();
    }

    public static boolean assertCheck(Node root){

        if(root == null) return true;
        /*
        0 to 2 are global x y z 
        3 to 12 are local varibales r1 to r10
        */
        int[] variables = new int[13];
        Node temp = root;
        while(temp != null){
            String LHS = temp.LHS;
            int indexoflhs = getIndex(LHS);
            if(temp.write)
                variables[indexoflhs] = Integer.parseInt(temp.RHS);
            else
                variables[indexoflhs] = variables[getIndex(temp.RHS)];
            temp = temp.next;
        }

        // print(variables);

        String[] splitOr = cond.split("or");
        for(int i = 0;i < splitOr.length;i++){
            String[] expressions = splitOr[i].split("and");
            boolean res = true;
            for(int j = 0;j < expressions.length;j++){
                res = res && evaluate(expressions[j] , variables);
            }
            if(res) return res;
        }

        return false;
    }

    public static boolean evaluate(String str , int[] values){
        String[] operators = {"==","!=","<=",">=","<",">"};

        for(int i = 0;i < operators.length;i++){
            String[] lhsrhs = str.split(operators[i]);
            if(lhsrhs.length <= 1)continue;
            
            
            if(operators[i].equals("=="))
                return values[getIndex(lhsrhs[0].trim())] == Integer.parseInt(lhsrhs[1].trim());
            else if(operators[i].equals("!="))
                return values[getIndex(lhsrhs[0].trim())] != Integer.parseInt(lhsrhs[1].trim());
            else if(operators[i].equals("<="))
                return values[getIndex(lhsrhs[0].trim())] <= Integer.parseInt(lhsrhs[1].trim());
            else if(operators[i].equals(">="))
                return values[getIndex(lhsrhs[0].trim())] >= Integer.parseInt(lhsrhs[1].trim());
            else if(operators[i].equals("<"))
                return values[getIndex(lhsrhs[0].trim())] < Integer.parseInt(lhsrhs[1].trim());
            else if(operators[i].equals(">"))
                return values[getIndex(lhsrhs[0].trim())] > Integer.parseInt(lhsrhs[1].trim());
            
        }

        return true;
    }

    public static void print(int[] variables){
        for(int i = 0;i < variables.length;i++){
            System.out.print(variables[i]+"  ");
        }
        System.out.println();
    }

    public static int getIndex(String str){
        String[] namesVar = {"x" , "y" , "z" , "r1" , "r2" , "r3" , "r4" , "r5" , "r6" , "r7", "r8", "r9", "r10"};
        int index = 0;
        for(int i = 1;i < namesVar.length;i++){
            if(str.equals(namesVar[i]))
                index = i;

        }
        return index;
    }
    
}

class Node {
    Node po;
    Node ws[];
    Node rf[];
    Node fr[];//Node[] fr;
    Node next;//execution
    String var;
    String LHS , RHS;
    boolean read;
    boolean write;
    int clock;
    int wsindex = 0 , rfindex = 0, frindex= 0; 
    boolean isSpecialNode = false;
    int programNum , instrcutionNumber;
    Node(){

        ws = new Node[40] ;
        rf = new Node[40] ;
        fr = new Node[40];
        
    }
}


class Solution{
    String trace;
    String rf;
    String ws;
}

/*
2
x=1;x=2;
x=3;x=4;
0
*/
