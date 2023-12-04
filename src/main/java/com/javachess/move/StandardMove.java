package com.javachess.move;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.piece.Piece;

public class StandardMove implements Move {

    protected Board board;
    protected Square srcSquare;
    protected Square dstSquare;
    protected Piece capturedPiece;

    //@ invariant board != null;

    /*@ requires board != null;
      @ ensures this.srcSquare == sourceSquare;
      @ ensures this.board == board;
      @ ensures this.dstSquare == targetSquare;
      @ pure
      @*/
    public StandardMove(Square sourceSquare, Square targetSquare, Board board) {
        this.srcSquare = sourceSquare;
        this.board = board;
        this.dstSquare = targetSquare;
    }

    /*@ ensures board.at(srcSquare) == null;
      @ ensures (dstSquare != null) 
      @         ==> (board.at(dstSquare) == \old(board.at(srcSquare)));
      @ ensures capturedPiece == \old(board.at(dstSquare));
      @ assignable board, capturedPiece 
      @*/
    @Override
    public void execute() {
        Piece sourcePiece = board.at(srcSquare);
        Piece targetPiece = board.at(dstSquare);

        board.removePieceAt(srcSquare);
        board.setPieceAt(dstSquare, sourcePiece);

        capturedPiece = targetPiece;
    }

    @Override
    /*@ ensures (dstSquare != null) ==> (board.at(dstSquare) == \old(capturedPiece));
      @ ensures (srcSquare != null && \old(board.at(dstSquare)) != null)
      @         ==>  board.at(srcSquare) == \old(board.at(dstSquare));
      @ ensures capturedPiece == null;
      @ assignable board, capturedPiece
      @*/
    public void undo() {
        Piece movedPiece = board.at(dstSquare);

        board.removePieceAt(dstSquare);
        board.setPieceAt(dstSquare, capturedPiece);
        board.setPieceAt(srcSquare, movedPiece);

        capturedPiece = null;
    }

    /*@ ensures \result == srcSquare;
      @ pure
      @*/
    @Override
    public Square getSource() {
        return srcSquare;
    }

    /*@ ensures \result == dstSquare;
      @ pure
      @*/
    @Override
    public Square getDst() {
        return dstSquare;
    }

    /*@ ensures \result == capturedPiece;
      @ pure
      @*/
    @Override
    public Piece getCapturedPiece() {
        return capturedPiece;
    }

    /*@ ensures \result == (srcSquare.equals(source) && dstSquare.equals(target));
      @ pure
      @*/
    @Override
    public boolean equals(Square source, Square target) {
        return getSource().equals(source) && getDst().equals(target);
    }
}
