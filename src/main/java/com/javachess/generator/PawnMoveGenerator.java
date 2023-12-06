package com.javachess.generator;

import java.util.ArrayList;
import java.util.List;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.move.Move;
import com.javachess.move.PawnPush;
import com.javachess.move.StandardMove;
import com.javachess.piece.Color;

public class PawnMoveGenerator implements MoveGenerator {
    /*@ also
      @  requires color != null && board != null && move != null;
      @  ensures \result <==>
      @          (
      @            move.dst.getCol() == move.source.getCol() &&
      @            move.dst.getRow() == move.source.getRow() + color.dir() &&
      @            board.isFree(move.dst)
      @          ) ||
      @          (
      @            move.dst.getCol() == move.source.getCol() &&
      @            move.dst.getRow() == move.source.getRow() + 2 * color.dir() &&
      @            board.isFree(move.dst) &&
      @            board.isFree(Square.atOffset(move.source, color.dir(), 0)) &&
      @            move.source.getRow() == color.pawnRow()
      @          ) ||
      @          (
      @            move.dst.getCol() == move.source.getCol() + 1 &&
      @            move.dst.getRow() == move.source.getRow() + color.dir() &&
      @            board.isColor(move.dst, color.opponent())
      @          ) ||
      @          (
      @            move.dst.getCol() == move.source.getCol() - 1 &&
      @            move.dst.getRow() == move.source.getRow() + color.dir() &&
      @            board.isColor(move.dst, color.opponent())
      @          );
      @ pure
      @ public model boolean isMoveCorrect(Color color, Board board, Move move);
      @*/

    /*@ code_bigint_math
      @ pure
      @*/
    @Override
    public List<Move> generateMoves(Square square, Color color, Board board) {
        List<Move> moves = new ArrayList<>();

        Square fwd = Square.atOffset(square, 1 * color.dir(), 0);
        Square push = Square.atOffset(square, 2 * color.dir(), 0);
        Square leftDiag = Square.atOffset(square, color.dir(), -1);
        Square rightDiag = Square.atOffset(square, color.dir(), 1);

        if (board.isFree(fwd)) {
            Move move = new StandardMove(square, fwd, board);

            moves.add(move);
        }

        if (square.getRow() == color.pawnRow() && board.isFree(fwd) && board.isFree(push)) {
            moves.add(new PawnPush(square, board));
        }

        if (board.isColor(rightDiag, color.opponent())) {
            moves.add(new StandardMove(square, rightDiag, board));
        }

        if (board.isColor(leftDiag, color.opponent())) {
            moves.add(new StandardMove(square, leftDiag, board));
        }

        //@ assert \forall Move m; ; moves.contains(m) ==> square == m.source;
        //@ assert \forall Move m; ; moves.contains(m) ==> m.dst != null;
        //@ assert \forall Move m; ; moves.contains(m) ==> m.dst.isValid();
        //@ assert \forall Move m; ; moves.contains(m) ==> MoveGeneratorHelper.isEmptyOrOpponent(m.dst, color, board);
        //@ assert \forall Move m; ; moves.contains(m) ==> isMoveCorrect(color, board, m);

        return moves;
    }
}
