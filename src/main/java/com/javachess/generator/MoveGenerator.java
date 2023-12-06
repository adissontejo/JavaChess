package com.javachess.generator;

import java.util.List;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.move.Move;
import com.javachess.piece.Color;

public interface MoveGenerator {
    /*@ pure
      @ model public boolean isMoveCorrect(Color color, Board board, Move move);
      @*/

    /*@ requires square != null && color != null && board != null;
      @ requires square.isValid();
      @ ensures \forall Move m; ; \result.contains(m) <==>
      @     square == m.source && 
      @     m.dst != null &&
      @     m.dst.isValid() &&
      @     MoveGeneratorHelper.isEmptyOrOpponent(m.dst, color, board) &&
      @     isMoveCorrect(color, board, m);
      @ pure
      @*/
    public List<Move> generateMoves(Square square, Color color, Board board);
}
