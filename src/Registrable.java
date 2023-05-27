public interface Registrable {
    void loanBook(Type type, String id, Student student);

    void tryReturnBook(Type type, String string, Student student);
}
