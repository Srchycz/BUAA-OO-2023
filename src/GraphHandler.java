import com.oocourse.spec3.main.Person;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Queue;

public class GraphHandler {
    private static void update(Path path, Path newPath) {
        if (newPath.getDist1() < path.getDist1()) {
            if (newPath.getOrigin1() != path.getOrigin1()) {
                path.update();
            }
            path.set1(newPath);
        }
        else if (newPath.getDist1() < path.getDist2()) {
            if (newPath.getOrigin1() != path.getOrigin1()) {
                path.set2(newPath);
            }
        }
    }

    public static int queryLeastMoment(int id, HashMap<Integer, Person> people) {
        //init
        HashMap<Integer, Path> paths = new HashMap<>();
        HashMap<Integer, Boolean> vis = new HashMap<>();
        for (Integer i : people.keySet()) {
            paths.put(i, new Path());
            vis.put(i, false);
        }
        vis.replace(id, true);
        MyPerson p = (MyPerson) people.get(id);
        for (Integer i : p.getAcquaintance().keySet()) {
            paths.get(i).setDist1(p.queryValue(i));
            paths.get(i).setOrigin1(i);
        }
        //dijkstra
        for (int i = 1; i < people.size(); ++ i) {
            int min = Integer.MAX_VALUE;
            int minId = -1;
            for (Integer j : people.keySet()) {
                if (!vis.get(j) && paths.get(j).getDist1() < min) {
                    min = paths.get(j).getDist1();
                    minId = j;
                }
            }
            if (minId == -1) {
                break;
            }
            vis.replace(minId, true);
            MyPerson minPerson = (MyPerson) people.get(minId);
            Path nowPath = paths.get(minId);
            for (Integer j : minPerson.getAcquaintance().keySet()) {
                if (!vis.get(j)) {
                    int value = minPerson.queryValue(j);
                    Path path = paths.get(j);
                    if (value > 0) {
                        update(path, new Path(nowPath.getDist1() + value, nowPath.getOrigin1()));
                        update(path, new Path(nowPath.getDist2() + value, nowPath.getOrigin2()));
                    }
                }
            }
        }
        //get result
        int res = 0x3f3f3f3f;
        for (Integer i : people.keySet()) {
            if (i != id) {
                res = Math.min(res, paths.get(i).getDist2() + paths.get(i).getDist1());
            }
        }
        return res == 0x3f3f3f3f ? -1 : res;
    }

    public static boolean isCircle(int id1, int id2, HashMap<Integer, Person> people) {
        HashMap<Integer, Integer> vis = new HashMap<>();
        vis.put(id1, id1);
        vis.put(id2, id2);
        Queue<Person> q1 = new LinkedList<>();
        Queue<Person> q2 = new LinkedList<>();
        q1.offer(people.get(id1));
        q2.offer(people.get(id2));
        while (!q1.isEmpty() && !q2.isEmpty()) {
            MyPerson now1 = (MyPerson) q1.poll();
            if (bfs(id2, id1, vis, q1, now1, people)) {
                return true;
            }
            MyPerson now2 = (MyPerson) q2.poll();
            assert now2 != null;
            if (bfs(id1, id2, vis, q2, now2, people)) {
                return true;
            }
        }
        return false;
    }

    private static boolean bfs(int aim, int id, HashMap<Integer, Integer> vis,
                               Queue<Person> queue, MyPerson now, HashMap<Integer, Person> people) {
        for (int i : now.getAcquaintance().keySet()) {
            if (vis.containsKey(i)) {
                if (vis.get(i) == aim) {
                    return true;
                }
                continue;
            }
            vis.put(i, id);
            queue.offer(people.get(i));
        }
        return false;
    }
}
