package com.javachess.move;

import com.javachess.board.Square;
import com.javachess.piece.Piece;

public interface Move {
    //@ public instance model Square source;
    //@ public instance model Square dst;
    //@ public instance model Piece theSourcePiece;
    //@ public instance model Piece theCapturedPiece;
    //@ public instance model com.javachess.board.Board theBoard;

    //@ public invariant source != null;
    //@ public invariant dst != null;
    //@ public invariant !source.equals(dst);
    //@ public invariant source.isValid();
    //@ public invariant dst.isValid();
    //@ public invariant theBoard != null;

    /*@ requires theBoard.at(source) != null;
      @ ensures theBoard.at(source) == null;
      @ ensures theBoard.at(dst) == \old(theBoard.at(source));
      @ ensures theCapturedPiece == \old(theBoard.at(dst));
      @ assigns theBoard.positions.objectState, theCapturedPiece;
      @*/
    public void execute();

    /*@ requires theBoard.at(source) == null;
      @ requires theBoard.at(dst) != null;
      @ ensures theBoard.at(dst) == \old(theCapturedPiece);
      @ ensures theBoard.at(source) == \old(theBoard.at(dst));
      @ ensures theCapturedPiece == null;
      @ assigns theBoard.positions.objectState, theCapturedPiece;
      @*/
    public void undo();

    /*@ ensures \result == theSourcePiece;
      @ pure
      @*/
    public Piece getSourcePiece();

    /*@ ensures \result == theCapturedPiece;
      @ pure
      @*/
    public Piece getCapturedPiece();

    /*@ ensures \result == source;
      @ pure
      @*/
    public Square getSource();

    /*@ ensures \result == dst;
      @ pure
      @*/
    public Square getDst();

    /*@ requires this.source != null && this.dst != null;
      @ ensures \result == (this.source.equals(src) && this.dst.equals(dst));
      @ pure
      @*/
    public boolean equals(Square src, Square dst);
}
