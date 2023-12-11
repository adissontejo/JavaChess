package com.javachess.generator;

import static com.javachess.generator.MoveGeneratorHelper.addVectorIfEmptyOrOpponent;

import java.util.ArrayList;
import java.util.List;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.move.Move;
import com.javachess.piece.Color;

public class QueenMoveGenerator implements MoveGenerator {
    /*@ also
      @   requires color != null && board != null && move != null;
      @   ensures \result <==>
      @           MoveGeneratorHelper.isInVectorEmptyOrOpponent(move.source, 1, 0, color, board, move.dst) ||
      @           MoveGeneratorHelper.isInVectorEmptyOrOpponent(move.source, -1, 0, color, board, move.dst) ||
      @           MoveGeneratorHelper.isInVectorEmptyOrOpponent(move.source, 0, 1, color, board, move.dst) ||
      @           MoveGeneratorHelper.isInVectorEmptyOrOpponent(move.source, 0, -1, color, board, move.dst) ||
      @           MoveGeneratorHelper.isInVectorEmptyOrOpponent(move.source, 1, 1, color, board, move.dst) ||
      @           MoveGeneratorHelper.isInVectorEmptyOrOpponent(move.source, 1, -1, color, board, move.dst) ||
      @           MoveGeneratorHelper.isInVectorEmptyOrOpponent(move.source, -1, 1, color, board, move.dst) ||
      @           MoveGeneratorHelper.isInVectorEmptyOrOpponent(move.source, -1, -1, color, board, move.dst);
      @ code_bigint_math
      @ pure
      @ public model boolean isMoveCorrect(Color color, Board board, Move move);
      @*/

    @Override
    public List<Move> generateMoves(Square square, Color color, Board board) {
        List<Move> moves = new ArrayList<>();

        moves.addAll(addVectorIfEmptyOrOpponent(square, 1, 0, color, board));
        moves.addAll(addVectorIfEmptyOrOpponent(square, -1, 0, color, board));
        moves.addAll(addVectorIfEmptyOrOpponent(square, 0, 1, color, board));
        moves.addAll(addVectorIfEmptyOrOpponent(square, 0, -1, color, board));
        moves.addAll(addVectorIfEmptyOrOpponent(square, 1, 1, color, board));
        moves.addAll(addVectorIfEmptyOrOpponent(square, 1, -1, color, board));
        moves.addAll(addVectorIfEmptyOrOpponent(square, -1, 1, color, board));
        moves.addAll(addVectorIfEmptyOrOpponent(square, -1, -1, color, board));

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
