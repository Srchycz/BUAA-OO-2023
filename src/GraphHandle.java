import com.oocourse.spec3.main.Person;

import java.util.HashMap;

public class GraphHandle {
    private static void update(Path path, Path newPath) {
        if (newPath.getDist1() > path.getDist1()) {
            if (newPath.getOrigin1() != path.getOrigin1()) {
                path.update();
            }
            path.set1(newPath);
        }
        else if (newPath.getDist1() > path.getDist2()) {
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
        for(Integer i : p.getAcquaintance().keySet()) {
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
                    if (value > 0 && paths.get(j).getDist1() > nowPath.getDist1() + value) {
                        update(path, new Path(nowPath.getDist1() + value, minId));
                    }
                    if (value > 0 && paths.get(j).getDist2() > paths.get(minId).getDist2() + value) {
                        update(path, new Path(nowPath.getDist2() + value, minId));
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
}
