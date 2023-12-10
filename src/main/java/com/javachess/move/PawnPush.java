package com.javachess.move;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.piece.Color;

public class PawnPush extends StandardMove {

    /*@ requires board != null && color != null && srcSquare != null;
      @ requires srcSquare.isValid();
      @ requires Square.atOffset(srcSquare, 2 * color.dir(), 0) != null;
      @ ensures source == srcSquare;
      @ ensures theBoard == board;
      @ ensures dst.col == srcSquare.col;
      @ ensures dst.row == srcSquare.row + 2 * color.dir();
      @ code_bigint_math
      @ pure
      @*/
    public PawnPush(Square srcSquare, Color color, Board board) {
        super(
            srcSquare,
            Square.atOffset(srcSquare, 2 * color.dir(), 0),
            board
        );
    }
}
