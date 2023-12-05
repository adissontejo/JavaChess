package com.javachess.board;

public class Square {
    //@ spec_public
    private final int col; //@ in theHashCode;
    //@ spec_public
    private final int row; //@ in theHashCode;

    /*@   requires col >= 0 && col < 8 && row >= 0 && row < 8;
      @   ensures \result.row == row && \result.col == col;
      @ also
      @   requires col < 0 || col >= 8 || row < 0 || row >= 8;
      @   ensures \result == null;
      @ pure
      @*/
    public static Square at(int row, int col) {
        Square newSquare = new Square(row, col);

        if (!newSquare.isValid()) {
            return null;
        }

        return newSquare;
    }

    /*@ requires square != null;
      @ {|
      @     requires square.row + row >= 0 &&
      @              square.row + row < 8 &&
      @              square.col + col >= 0 &&
      @              square.col + col < 8;
      @     ensures \result.row == square.row + row && \result.col == square.col + col;
      @   also
      @     requires square.row + row < 0 ||
      @              square.row + row >= 8 ||
      @              square.col + col < 0 ||
      @              square.col + col >= 8;
      @     ensures \result == null;
      @ |}
      @ code_bigint_math
      @ pure
      @*/
    public static Square atOffset(Square square, int row, int col) {
        Square newSquare = new Square(square.getRow() + row, square.getCol() + col);

        if (!newSquare.isValid()) {
            return null;
        }

        return newSquare;
    }

    /*@ ensures this.col == column;
      @ ensures this.row == row;
      @ pure
      @*/
    private Square(int row, int column) {
        this.col = column;
        this.row = row;
    }

    /*@ ensures \result == this.col;
      @ pure
      @*/
    public int getCol() {
        return col;
    }

    /*@ ensures \result == this.row;
      @ pure
      @*/
    public int getRow() {
        return row;
    }

    /*@ ensures \result == (col >= 0 && col < 8 && row >= 0 && row < 8);
      @ pure
      @*/
    public boolean isValid() {
        return col >= 0 && col < 8 && row >= 0 && row < 8;
    }

    //@ public represents theHashCode = 31 * (31 + col) + row;

    /*@ also
      @   ensures \result == 31 * (31 + col) + row;
      @   code_bigint_math
      @*/
    @Override
    public int hashCode() {
        final int prime = 31;

        return prime * (prime + col) + row;
    }

    /*@ also
      @   requires this == obj;
      @   ensures \result;
      @ also
      @   requires this != obj;
      @   {|
      @     requires obj == null;
      @     ensures !\result;
      @   also
      @     requires obj != null;
      @     {|
      @       requires getClass() != obj.getClass();
      @       ensures !\result;
      @     also
      @       requires getClass() == obj.getClass();
      @       ensures \result == (col == ((Square) obj).col && row == ((Square) obj).row);
      @     |}
      @   |}
      @ pure
      @*/
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        Square other = (Square) obj;
        if (col != other.col) {
            return false;
        }
        if (row != other.row) {
            return false;
        }
        return true;
    }
}
