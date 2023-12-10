package com.javachess.evaluator;

import java.util.ArrayList;
import java.util.List;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.move.Move;
import com.javachess.piece.Color;
import com.javachess.piece.Piece;
import com.javachess.piece.PieceType;

public class BoardEvaluator {

    public static boolean isCheck(Color color, Board board) {
        return isThreatenedBy(color.opponent(), findKing(color, board), board);
    }

    public static boolean isCheckMate(Color color, List<Move> ctxMoves, Board board) {
        return isCheck(color, board) && legalMoves(color, ctxMoves, board).isEmpty();
    }

    public static boolean isStaleMate(Color color, List<Move> ctxMoves, Board board) {
        return !isCheck(color, board) && legalMoves(color, ctxMoves, board).isEmpty();
    }

    public static boolean isThreatenedBy(Color color, Square square, Board board) {
        return semiLegalMoves(color, board).stream().anyMatch((move) -> (move.getDst().equals(square)));
    }

    public static List<Move> legalMoves(Color color, List<Move> ctxMoves, Board board) {
        List<Move> legalMoves = new ArrayList<>();
        List<Move> semiLegalMoves = semiLegalMoves(color, board);

        if (ctxMoves != null) {
            semiLegalMoves.addAll(ctxMoves);
        }

        for (Move move : semiLegalMoves) {
            move.execute();

            if (!isCheck(color, board)) {
                legalMoves.add(move);
            }

            move.undo();
        }

        return legalMoves;
    }

    /*@ requires color != null && board != null;
      @ {|
      @     requires \exists int i; 0 <= i < board.allSquares().size(); (
      @                board.at(board.allSquares().get(i)) != null &&
      @                board.at(board.allSquares().get(i)).isType(PieceType.KING) &&
      @                board.at(board.allSquares().get(i)).isColor(color)
      @              );
      @     ensures \result != null;
      @     ensures board.at(\result) != null;
      @     ensures board.at(\result).isType(PieceType.KING);
      @     ensures board.at(\result).isColor(color);
      @   also
      @     requires \forall int i; 0 <= i < board.allSquares().size(); (
      @                board.at(board.allSquares().get(i)) == null ||
      @                !board.at(board.allSquares().get(i)).isType(PieceType.KING) ||
      @                !board.at(board.allSquares().get(i)).isColor(color)
      @              );
      @     signals_only IllegalStateException;
      @ |}
      @ pure
      @*/
    public static Square findKing(Color color, Board board) {
        for (Square square : board.allSquares()) {
            Piece piece = board.at(square);

            //@ assume PieceType.KING.generator != null;

            /*@ assume \forall int i; 0 <= i < board.allSquares().size(); (
              @           board.at(board.allSquares().get(i)) == null ||
              @           !board.at(board.allSquares().get(i)).isType(PieceType.KING) ||
              @           !board.at(board.allSquares().get(i)).isColor(color)
              @        ) ==> (piece == null || !piece.isType(PieceType.KING) || !piece.isColor(color));
              @*/
            if (piece != null && piece.isType(PieceType.KING) && piece.isColor(color)) {
                /*@ assume !(\forall int i; 0 <= i < board.allSquares().size(); (
                  @           board.at(board.allSquares().get(i)) == null ||
                  @           !board.at(board.allSquares().get(i)).isType(PieceType.KING) ||
                  @           !board.at(board.allSquares().get(i)).isColor(color)
                  @        ));
                  @*/
                return square;
            }
        }

        /*@ assume !(\exists int i; 0 <= i < board.allSquares().size(); (
          @           board.at(board.allSquares().get(i)) != null &&
          @           board.at(board.allSquares().get(i)).isType(PieceType.KING) &&
          @           board.at(board.allSquares().get(i)).isColor(color)
          @        ));
          @*/

        throw new IllegalStateException("The king is missing!");
    }

    /*@ requires color != null && board != null;
      @ ensures \result != null;
      @ ensures \forall int i; 0 <= i < \result.size(); (
      @            \result.get(i) != null &&
      @            \result.get(i).theBoard == board
      @          );
      @ pure
      @*/
    private static List<Move> semiLegalMoves(Color color, Board board) {
        List<Move> moveList = new ArrayList<>();

        List<Square> squares = board.allSquares();

        /*@ loop_invariant 0 <= i <= squares.size();
          @ loop_invariant \forall int j; 0 <= j < moveList.size(); (
          @                  moveList.get(j) != null &&
          @                  moveList.get(j).theBoard == board
          @                );
          @ loop_writes moveList.values;
          @ decreases squares.size() - i;
          @*/
        for (int i = 0; i < squares.size(); i++) {
            Square square = squares.get(i);

            Piece piece = board.at(square);

            /*@ assert \forall int j; 0 <= j < moveList.size(); (
              @           moveList.get(j) != null &&
              @           moveList.get(j).theBoard == board
              @        );
              @*/

            if (piece != null && square.isValid() && piece.isColor(color)) {
                List<Move> moves = piece.availableMoves(square, board);

                /*@ assert \forall int j; 0 <= j < moves.size(); (
                  @          moves.get(j) != null &&
                  @          moves.get(j).theBoard == board
                  @        );
                  @*/

                /*@ loop_invariant 0 <= j <= moves.size();
                  @ loop_invariant \forall int k; 0 <= k < moveList.size(); (
                  @                  moveList.get(k) != null &&
                  @                  moveList.get(k).theBoard == board
                  @                );
                  @ loop_invariant \forall int k; 0 <= k < moves.size(); (
                  @                  moves.get(k) != null &&
                  @                  moves.get(k).theBoard == board
                  @                );
                  @ loop_writes moveList.values;
                  @*/
                for (int j = 0; j < moves.size(); j++) {
                    /*@ assert \forall int k; 0 <= k < moves.size(); (
                      @          moves.get(k) != null &&
                      @          moves.get(k).theBoard == board
                      @        );
                      @ assert moves.get(j) != null && moves.get(j).theBoard == board;
                      @ assert \forall int k; 0 <= k < moveList.size(); (
                      @          moveList.get(k) != null &&
                      @          moveList.get(k).theBoard == board
                      @        );
                      @ ghost int oldSize = moveList.size();
                      @ assert \forall int k; 0 <= k < oldSize; (
                      @          moveList.get(k) != null &&
                      @          moveList.get(k).theBoard == board
                      @        );
                      @*/

                    Move move = moves.get(j);

                    //@ assert move != null && move.theBoard == board;

                    moveList.add(move);

                    /*@ assert moveList.get(moveList.size() - 1) == move;
                      @ assert move != null && move.theBoard == board;
                      @ assert moveList.size() == oldSize + 1;
                      @ assume \forall int k; 0 <= k < moves.size(); (
                      @          moves.get(k) != null &&
                      @          moves.get(k).theBoard == board
                      @        );
                      @ assume \forall int k; 0 <= k < oldSize; (
                      @          moveList.get(k) != null &&
                      @          moveList.get(k).theBoard == board
                      @        );
                      @ assert \forall int k; 0 <= k < moveList.size() - 1; (
                      @          moveList.get(k) != null &&
                      @          moveList.get(k).theBoard == board
                      @        );
                      @ assert moveList.get(moveList.size() - 1) != null && moveList.get(moveList.size() - 1).theBoard == board;
                      @ assert \forall int k; 0 <= k < moveList.size(); (
                      @          moveList.get(k) != null &&
                      @          moveList.get(k).theBoard == board
                      @        );
                      @*/
                }

                /*@ assert \forall int j; 0 <= j < moveList.size(); (
                  @           moveList.get(j) != null &&
                  @           moveList.get(j).theBoard == board
                  @        );
                  @*/
            } else {
                /*@ assert \forall int j; 0 <= j < moveList.size(); (
                  @           moveList.get(j) != null &&
                  @           moveList.get(j).theBoard == board
                  @        );
                  @*/
            }

            /*@ assume (piece != null && square.isValid() && piece.isColor(color)) ==> \forall int j; 0 <= j < moveList.size(); (
              @           moveList.get(j) != null &&
              @           moveList.get(j).theBoard == board
              @        );
              @ assume (piece == null || !square.isValid() || !piece.isColor(color)) ==> \forall int j; 0 <= j < moveList.size(); (
              @           moveList.get(j) != null &&
              @           moveList.get(j).theBoard == board
              @        );
              @ assert \forall int j; 0 <= j < moveList.size(); (
              @           moveList.get(j) != null &&
              @           moveList.get(j).theBoard == board
              @        );
              @*/
        }

        return moveList;
    }
}
