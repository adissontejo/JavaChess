package com.javachess.generator;

import java.util.ArrayList;
import java.util.List;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.move.Move;
import com.javachess.move.StandardMove;
import com.javachess.piece.Color;

public class MoveGeneratorHelper {
    /*@ requires color != null && moves != null && board != null;
      @ {|
      @     requires src != null && dst != null;
      @     requires (board.isFree(dst) || board.isColor(dst, color.opponent()));
      @     ensures moves.size() == \old(moves.size()) + 1;
      @     ensures moves.get(moves.size() - 1).source == src;
      @     ensures moves.get(moves.size() - 1).dst == dst;
      @     assignable moves.values;
      @   also
      @     requires src == null || dst == null;
      @     assignable \nothing;
      @   also
      @     requires !board.isFree(dst) && !board.isColor(dst, color.opponent());
      @     assignable \nothing;
      @ |}
      @*/
    public static void addMoveIfEmptyOrOpponent(final Square src, final Square dst, final Color color,
            final List<Move> moves, final Board board) {
        if (src == null || dst == null) {
            return;
        }

        if (board.isFree(dst) || board.isColor(dst, color.opponent())) {
            Move move = new StandardMove(src, dst, board);

            //@ assert move.source == src;
            //@ assert move.dst == dst;

            moves.add(move);
        }
    }

    public static List<Move> addVectorIfEmptyOrOpponent(final Square src, final int rowOffset, final int colOffset,
            final Color color, final Board board) {
        List<Move> moves = new ArrayList<>();

        Square square = Square.atOffset(src, rowOffset, colOffset);

        while (board.isFree(square) || board.isColor(square, color.opponent())) {
            moves.add(new StandardMove(src, square, board));
            square = Square.atOffset(square, rowOffset, colOffset);
        }

        return moves;
    }
}
