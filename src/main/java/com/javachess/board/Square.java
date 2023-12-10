package com.javachess.board;

public class Square {
    //@ spec_public
    private final int col; //@ in theHashCode;
                           //@ in uniqueHash;
    //@ spec_public
    private final int row; //@ in theHashCode;
                           //@ in uniqueHash;

    /*@   requires col >= 0 && col < 8 && row >= 0 && row < 8;
      @   ensures \result != null;
      @   ensures \result.row == row && \result.col == col;
      @ also
      @   requires col < 0 || col >= 8 || row < 0 || row >= 8;
      @   ensures \result == null;
      @ pure
      @*/
    public static Square at(int row, int col) {
        Square newSquare = new Square(row, col);

        //@ assert newSquare.row == row && newSquare.col == col;
        //@ assert col >= 0 && col < 8 && row >= 0 && row < 8 <==> newSquare.isValid();

        if (!newSquare.isValid()) {
            return null;
        }

        //@ assert col >= 0 && col < 8 && row >= 0 && row < 8;
        //@ assert newSquare.row == row && newSquare.col == col;

        return newSquare;
    }

    /*@ requires square != null;
      @ {|
      @   requires at(square.row + row, square.col + col) != null;
      @   ensures \result != null;
      @   ensures \result.row == square.row + row && \result.col == square.col + col;
      @ also
      @   requires at(square.row + row, square.col + col) == null;
      @   ensures \result == null;
      @ |}
      @ code_bigint_math
      @ pure
      @*/
    public static Square atOffset(Square square, int row, int col) {
        Square newSquare = at(square.getRow() + row, square.getCol() + col);

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

    /*@ ensures \result <==> (col >= 0 && col < 8 && row >= 0 && row < 8);
      @ pure
      @*/
    public boolean isValid() {
        return col >= 0 && col < 8 && row >= 0 && row < 8;
    }

    //@ public represents theHashCode = 31 * (31 + col) + row;
    //@ public represents uniqueHash = 31 * (31 + col) + row;

    /*@ code_bigint_math
      @ pure
      @*/
    @Override
    public int hashCode() {
        final int prime = 31;

        return prime * (prime + col) + row;
    }

    /*@ also
      @  requires obj != null;
      @  requires getClass() == obj.getClass();
      @  ensures \result <==> theHashCode == ((Square) obj).theHashCode;
      @ also
      @  requires obj != null;
      @  requires getClass() != obj.getClass();
      @  ensures \result == false;
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

        return other.hashCode() == hashCode();
    }
}
