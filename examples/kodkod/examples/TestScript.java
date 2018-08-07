package kodkod.examples;

import java.io.*;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;

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
                try {
                    System.out.println(testClass.getName() + " is being tested.");
                    out.println(testClass.getName() + " is being tested.");
                    out.flush();

                    for (int i = 0; i < testCount; i++) {

                        System.out.println("Test " + (i + 1) + " is started.");
                        out.println("Test " + (i + 1) + " is started.");
                        out.flush();

                        long time = System.currentTimeMillis();
                        testClass.getMethod("main", String[].class).invoke(null, new Object[]{new String[0]});
                        time = System.currentTimeMillis() - time;

                        System.out.println("Time: " + time + " ms");
                        out.println("Time: " + time + " ms");
                        out.flush();
                    }

                    out.println();
                    out.flush();

                } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
                    e.printStackTrace();
                }
            });
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
