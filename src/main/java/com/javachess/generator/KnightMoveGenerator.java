package com.javachess.generator;

import static com.javachess.generator.MoveGeneratorHelper.addMoveIfEmptyOrOpponent;

import java.util.ArrayList;
import java.util.List;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.move.Move;
import com.javachess.piece.Color;

public class KnightMoveGenerator implements MoveGenerator {
    /*@ also
      @   requires color != null && board != null && move != null;
      @   ensures \result <==>
      @           (
      @             move.dst.getRow() == move.source.getRow() + 1
      @             && move.dst.getCol() == move.source.getCol() + 2
      @           ) ||
      @           (
      @             move.dst.getRow() == move.source.getRow() - 1
      @             && move.dst.getCol() == move.source.getCol() + 2
      @           ) ||
      @           (
      @             move.dst.getRow() == move.source.getRow() + 1
      @             && move.dst.getCol() == move.source.getCol() - 2
      @           ) ||
      @           (
      @             move.dst.getRow() == move.source.getRow() - 1
      @             && move.dst.getCol() == move.source.getCol() - 2
      @           ) ||
      @           (
      @             move.dst.getRow() == move.source.getRow() + 2
      @             && move.dst.getCol() == move.source.getCol() + 1
      @           ) ||
      @           (
      @             move.dst.getRow() == move.source.getRow() - 2
      @             && move.dst.getCol() == move.source.getCol() + 1
      @           ) ||
      @           (
      @             move.dst.getRow() == move.source.getRow() + 2
      @             && move.dst.getCol() == move.source.getCol() - 1
      @           ) ||
      @           (
      @             move.dst.getRow() == move.source.getRow() - 2
      @             && move.dst.getCol() == move.source.getCol() - 1
      @           );
      @ code_bigint_math
      @ pure
      @ public model boolean isMoveCorrect(Color color, Board board, Move move);
      @*/

    /*@ code_bigint_math
      @ pure
      @*/
    @Override
    public List<Move> generateMoves(Square square, Color color, Board board) {
        List<Move> moves = new ArrayList<>();

        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, 2, 1), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, 2, -1), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, -2, 1), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, -2, -1), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, 1, 2), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, 1, -2), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, -1, 2), color, moves, board);
        addMoveIfEmptyOrOpponent(square, Square.atOffset(square, -1, -2), color, moves, board);

        //@ assert \forall Move m; ; moves.contains(m) ==> square == m.source;
        //@ assert \forall Move m; ; moves.contains(m) ==> m.dst != null;
        //@ assert \forall Move m; ; moves.contains(m) ==> m.dst.isValid();
        //@ assert \forall Move m; ; moves.contains(m) ==> MoveGeneratorHelper.isEmptyOrOpponent(m.dst, color, board);
        //@ assert \forall Move m; ; moves.contains(m) ==> isMoveCorrect(color, board, m);

        return moves;
    }
}
