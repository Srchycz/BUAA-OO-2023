public class Path {
    static final int INF = 0x3f3f3f3f;
    private int dist1;
    private int dist2;
    private int origin1;
    private int origin2;

    public Path() {
        this.dist1 = INF;
        this.dist2 = INF;
        this.origin1 = -1;
        this.origin2 = -1;
    }

    public Path(int dist1, int origin1) {
        this.dist1 = dist1;
        this.dist2 = INF;
        this.origin1 = origin1;
        this.origin2 = -1;
    }

    public void update() {
        dist2 = dist1;
        origin2 = origin1;
    }

    public void set1(Path p) {
        this.dist1 = p.getDist1();
        this.origin1 = p.getOrigin1();
    }

    public void set2(Path p) {
        this.dist2 = p.getDist1();
        this.origin2 = p.getOrigin1();
    }

    public int getDist1() {
        return dist1;
    }

    public void setDist1(int dist1) {
        this.dist1 = dist1;
    }

    public int getDist2() {
        return dist2;
    }

    public void setDist2(int dist2) {
        this.dist2 = dist2;
    }

    public int getOrigin1() {
        return origin1;
    }

    public void setOrigin1(int origin1) {
        this.origin1 = origin1;
    }

    public int getOrigin2() {
        return origin2;
    }

    public void setOrigin2(int origin2) {
        this.origin2 = origin2;
    }
}
