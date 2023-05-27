//Singleton
public class Calendar {
    private Calendar() {
        year = 2023;
        month = 1;
        day = 1;
    }

    private static class CalendarHolder {
        private static final Calendar INSTANCE = new Calendar();
    }

    public static Calendar getInstance() {
        return CalendarHolder.INSTANCE;
    }

    private int year;
    private int month;
    private int day;
    private final int[] limit = {0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};

    public String getDate() {
        return String.format("[%4d-%02d-%02d]", year, month, day);
    }

    public void nextDay() {
        ++ day;
        if (day > limit[month]) {
            day = 1;
            ++ month;
            if (month > 12) {
                month = 1;
                ++ year;
            }
        }
    }

}
