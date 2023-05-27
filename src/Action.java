public enum Action {
    BORROW, LOSE, SMEAR, RETURN;
    public static Action getAction(String action) {
        switch (action) {
            case "borrowed":
                return BORROW;
            case "lost":
                return LOSE;
            case "smeared":
                return SMEAR;
            case "returned":
                return RETURN;
            default:
                throw new RuntimeException("Error: Invalid action.");
        }
    }
}
