package com.javachess.move.castling;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.move.Move;
import com.javachess.piece.Color;

public class CastlingQueenSide extends Castling {
    //@ public represents isKingSide = false;

    /*@ requires color != null && board != null;
      @ ensures this.sourcePiece.color == color;
      @ ensures this.sourcePiece.type == com.javachess.piece.PieceType.KING;
      @ ensures this.board == board;
      @*/
    public CastlingQueenSide(Color color, Board board) {
        super(color, board);
    }

    @Override
    public Square getDst() {
        return Square.atOffset(kingSquare, 0, -2);
    }

    @Override
    protected Square getRookSrc() {
        return Square.atOffset(kingSquare, 0, -4);
    }

    @Override
    protected Square getRookDst() {
        return Square.atOffset(kingSquare, 0, -1);
    }

    @Override
    public Move copy() {
        return new CastlingQueenSide(this.sourcePiece.color(), board.copy());
    }
}
