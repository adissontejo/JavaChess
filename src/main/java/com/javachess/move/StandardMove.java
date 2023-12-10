package com.javachess.move;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.piece.Piece;

public class StandardMove implements Move {
    //@ spec_public
    protected Board board; //@ in theBoard;
    //@ spec_public
    protected Square srcSquare; //@ in source;
    //@ spec_public
    protected Square dstSquare; //@ in dst;
    //@ spec_public
    protected Piece capturedPiece; //@ in theCapturedPiece;

    //@ public represents theBoard = board;
    //@ public represents source = srcSquare;
    //@ public represents dst = dstSquare;
    //@ public represents theCapturedPiece = capturedPiece;

    /*@ requires board != null && sourceSquare != null && targetSquare != null;
      @ requires sourceSquare.isValid() && targetSquare.isValid();
      @ requires !sourceSquare.equals(targetSquare);
      @ ensures source == sourceSquare;
      @ ensures dst == targetSquare;
      @ ensures theBoard == board;
      @ pure
      @*/
    public StandardMove(Square sourceSquare, Square targetSquare, Board board) {
        this.srcSquare = sourceSquare;
        this.board = board;
        this.dstSquare = targetSquare;
    }

    @Override
    public void execute() {
        Piece sourcePiece = board.at(srcSquare);
        Piece targetPiece = board.at(dstSquare);

        board.removePieceAt(srcSquare);
        board.setPieceAt(dstSquare, sourcePiece);

        capturedPiece = targetPiece;
    }

    @Override
    public void undo() {
        Piece movedPiece = board.at(dstSquare);

        board.removePieceAt(dstSquare);
        //@ assert board.at(dstSquare) == null;
        board.setPieceAt(dstSquare, capturedPiece);
        //@ assert board.at(dstSquare) == capturedPiece;
        board.setPieceAt(srcSquare, movedPiece);

        capturedPiece = null;
    }

    @Override
    public Square getSource() {
        return srcSquare;
    }

    @Override
    public Square getDst() {
        return dstSquare;
    }

    @Override
    public Piece getCapturedPiece() {
        return capturedPiece;
    }

    @Override
    public boolean equals(Square source, Square target) {
        return getSource().equals(source) && getDst().equals(target);
    }
}
