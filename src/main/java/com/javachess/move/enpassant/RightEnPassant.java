package com.javachess.move.enpassant;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.piece.Piece;

public class RightEnPassant extends EnPassant {

    public RightEnPassant(Square srcSquare, Board board) {
        super(srcSquare, board);
    }

    @Override
    protected Square getDstSquare(Square srcSquare) {
        Piece piece = board.at(srcSquare);
        return Square.at(srcSquare.getRow() + piece.color().dir(), srcSquare.getCol() + 1);
    }

    @Override
    protected Square getCapturedSquare(Square srcSquare) {
        return Square.at(srcSquare.getRow(), srcSquare.getCol() + 1);
    }
}
