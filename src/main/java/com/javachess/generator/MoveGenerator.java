package com.javachess.generator;

import java.util.List;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.move.Move;
import com.javachess.piece.Color;

public interface MoveGenerator {
    //@ public instance model boolean isLegal;

    /*@ requires square != null && color != null && move != null && board != null;
      @ requires square.isValid();
      @ ensures \result <==>
      @         (move.source == square) &&
      @         (move.dst != null && move.getDst().isValid()) &&
      @         (board.at(move.dst) == null || board.isColor(move.dst, color.opponent()));
      @ pure
      @ model public boolean isMoveValid(Square square, Color color, Board board, Move move);
      @*/

    /*@ pure
      @ model public boolean isMoveSemiLegal(Square square, Color color, Board board, Move move);
      @*/

    /*@ requires square != null && color != null && board != null;
      @ ensures \forall Move m; ; \result.contains(m) <==> isMoveSemiLegal(square, color, board, m);
      @ pure
      @*/
    public List<Move> generateMoves(Square square, Color color, Board board);
}
