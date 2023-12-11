package com.javachess.generator;

import static com.javachess.generator.MoveGeneratorHelper.addMoveIfEmptyOrOpponent;

import java.util.ArrayList;
import java.util.List;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.move.Move;
import com.javachess.piece.Color;

public class KingMoveGenerator implements MoveGenerator {
    /*@ also
      @   requires color != null && board != null && move != null;
      @   ensures \result <==> MoveGeneratorHelper.isEmptyOrOpponent(move.dst, color, board) && (
      @           (
      @             move.dst.getRow() == move.source.getRow() + 1 &&
      @             move.dst.getCol() == move.source.getCol()
      @           ) || (
      @             move.dst.getRow() == move.source.getRow() - 1 &&
      @             move.dst.getCol() == move.source.getCol()
      @           ) || (
      @             move.dst.getRow() == move.source.getRow() &&
      @             move.dst.getCol() == move.source.getCol() + 1
      @           ) || (
      @             move.dst.getRow() == move.source.getRow() &&
      @             move.dst.getCol() == move.source.getCol() - 1
      @           ) || (
      @             move.dst.getRow() == move.source.getRow() + 1 &&
      @             move.dst.getCol() == move.source.getCol() + 1
      @           ) || (
      @             move.dst.getRow() == move.source.getRow() + 1 &&
      @             move.dst.getCol() == move.source.getCol() - 1
      @           ) || (
      @             move.dst.getRow() == move.source.getRow() - 1 &&
      @             move.dst.getCol() == move.source.getCol() + 1
      @           ) || (
      @             move.dst.getRow() == move.source.getRow() - 1 &&
      @             move.dst.getCol() == move.source.getCol() - 1
      @           ));
      @ code_bigint_math
      @ pure
      @ public model boolean isMoveCorrect(Color color, Board board, Move move);
      @*/

    @Override
    public List<Move> generateMoves(Square square, Color color, Board board) {
        List<Move> moves = new ArrayList<>();

        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, 1, 0), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, -1, 0), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, 1, 1), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, 1, -1), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, -1, 1), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, -1, -1), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, 0, 1), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, 0, -1), color, moves, board);

        /*@ assume \forall int i; 0 <= i < moves.size(); (
          @   moves.get(i) != null &&
          @   moves.get(i).source == square &&
          @   moves.get(i).theBoard == board &&
          @   moves.get(i).theSourcePiece == board.at(square) &&
          @   isMoveCorrect(color, board, moves.get(i))
          @ );
          @ assume \forall Move m;
          @        m != null &&
          @        m.source == square &&
          @        m.theBoard == board &&
          @        m.theSourcePiece == board.at(square) &&
          @        isMoveCorrect(color, board, m);
          @        (
          @          \exists int i; 0 <= i < moves.size();
          @          moves.get(i).equals(m.source, m.dst)
          @        );
          @*/

        return moves;
    }
}
