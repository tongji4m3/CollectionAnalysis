package test;


import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

public class MainTest
{
    public static void main(String[] args)
    {
        LinkedList<Integer> linkedList = new LinkedList<>();
        for (int i = 0; i < 5; i++) {
            linkedList.add(i);
        }

        for (Integer integer : linkedList) {
            System.out.println(integer);
        }
    }
}
