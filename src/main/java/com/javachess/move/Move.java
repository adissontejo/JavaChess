package com.javachess.move;

import com.javachess.board.Square;
import com.javachess.piece.Piece;

public interface Move {
    //@ public instance model Square source;
    //@ public instance model Square dst;
    //@ public instance model Piece theCapturedPiece;
    //@ public instance model com.javachess.board.Board theBoard;

    //@ public invariant theBoard != null;

    /*@ ensures theBoard.at(source) == null;
      @ ensures (dst != null)
      @         ==> (theBoard.at(dst) == \old(theBoard.at(source)));
      @ ensures theCapturedPiece == \old(theBoard.at(dst));
      @ assigns theBoard, theCapturedPiece;
      @*/
    public void execute();

    /*@ ensures (dst != null) ==> (theBoard.at(dst) == \old(theCapturedPiece));
      @ ensures (source != null && \old(theBoard.at(dst)) != null)
      @         ==>  theBoard.at(source) == \old(theBoard.at(dst));
      @ ensures theCapturedPiece == null;
      @ assigns theBoard, theCapturedPiece;
      @*/
    public void undo();

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

    /*@ ensures \result == (this.source.equals(src) && this.dst.equals(dst));
      @ pure
      @*/
    public boolean equals(Square src, Square dst);
}
