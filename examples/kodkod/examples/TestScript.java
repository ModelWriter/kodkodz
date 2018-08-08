package kodkod.examples;

import java.io.*;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class TestScript {

    private final static int testCount = 5;

    public static void main(String[] args) throws Exception {
        List<Class> classes = getClasses(TestScript.class.getClassLoader(),"kodkod/examples/models");
        for(Class c:classes){
            System.out.println("Class: "+c);
        }

        try (PrintWriter out = new PrintWriter("test_script.out")) {
            out.println(new Date().toLocaleString());
            out.println();
            out.flush();
            classes.forEach(testClass -> {
                    System.out.println(testClass.getName() + " is being tested.");
                    out.println(testClass.getName() + " is being tested.");
                    out.flush();

                    for (int i = 0; i < testCount; i++) {

                        final int testNo = i + 1;

                        System.out.println("Test " + testNo + " is started.");

                        boolean[] flag = new boolean[] {false};

                        ExecutorService executorService = Executors.newSingleThreadExecutor();

                        executorService.submit(() -> {
                            long time = System.currentTimeMillis();
                            try {
                                testClass.getMethod("main", String[].class).invoke(null, new Object[]{new String[0]});
                            } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
                                e.printStackTrace();
                            }
                            time = System.currentTimeMillis() - time;

                            flag[0] = true;

                            System.out.println("Time: " + time + " ms");
                            out.println("Test " + testNo + ": " + time + " ms");
                            out.flush();

                            executorService.shutdown();
                        });

                        try {
                            executorService.awaitTermination(60, TimeUnit.SECONDS);
                        } catch (InterruptedException e) {
                            e.printStackTrace();
                        }

                        if (!flag[0]) {
                            System.out.println("Couldn't solve in 60 seconds");
                            System.out.println("Aborting...");
                            out.println("Test " + testNo + ": Couldn't solve in 60 seconds");
                            out.println("Aborting...");
                            out.flush();
                            break;
                        }
                    }

                    out.println();
                    out.flush();
            });

            System.out.println("Finished.");
            out.println("Finished.");
            out.flush();
        }
        catch (FileNotFoundException e) {
            e.printStackTrace();
        }
    }

    private static List<Class> getClasses(ClassLoader cl, String pack) throws Exception{

        String dottedPackage = pack.replaceAll("[/]", ".");
        List<Class> classes = new ArrayList<Class>();
        URL upackage = cl.getResource(pack);

        assert upackage != null;
        DataInputStream dis = new DataInputStream((InputStream) upackage.getContent());
        String line;
        while ((line = dis.readLine()) != null) {
            if(line.endsWith(".class")) {
                classes.add(Class.forName(dottedPackage+"."+line.substring(0,line.lastIndexOf('.'))));
            }
            else {
                classes.addAll(getClasses(cl, pack + "/" + line));
            }
        }
        return classes;
    }

}
