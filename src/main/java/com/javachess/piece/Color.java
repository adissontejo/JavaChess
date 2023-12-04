package com.javachess.piece;

public enum Color {

    BLACK(-1, 6), WHITE(1, 1);

    //@ spec_public
    private final int value;
    //@ spec_public
    private final int pawnRow;

    /*@ ensures this.value == value;
      @ ensures this.pawnRow == pawnRow;
      @ pure
      @*/
    private Color(int value, int pawnRow) {
        this.value = value;
        this.pawnRow = pawnRow;
    }

    /*@ ensures \result == value;
      @ pure
      @*/
    public int dir() {
        return value;
    }

    /*@ ensures \result == pawnRow;
      @ pure
      @*/
    public int pawnRow() {
        return pawnRow;
    }

    /*@
      @   requires this == Color.BLACK;
      @   ensures \result == Color.WHITE;
      @ also
      @   requires this == Color.WHITE;
      @   ensures \result == Color.BLACK;
      @*/
    public Color opponent() {
        if (this == Color.BLACK) {
            return Color.WHITE;
        } else {
            return Color.BLACK;
        }
    }
}
