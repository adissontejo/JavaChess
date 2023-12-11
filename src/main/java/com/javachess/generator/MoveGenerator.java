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
      @ ensures \result != null;
      @ ensures \forall int i; 0 <= i < \result.size(); (
      @   \result.get(i) != null &&
      @   \result.get(i).source == square &&
      @   \result.get(i).theBoard == board &&
      @   \result.get(i).theSourcePiece == board.at(square) &&
      @   isMoveCorrect(color, board, \result.get(i))
      @ );
      @ ensures \forall Move m; m != null && m.source == square && m.theBoard == board && m.theSourcePiece == board.at(square) && isMoveCorrect(color, board, m); (
      @           \exists int i; 0 <= i < \result.size(); \result.get(i).equals(m.source, m.dst)
      @         );
      @ ensures \fresh(\result);
      @ pure
      @*/
    public List<Move> generateMoves(Square square, Color color, Board board);
}
