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
    /*@ requires color != null && board != null;
      @ ensures \result <==> isThreatenedBy(color.opponent(), findKing(color, board), board);
      @ pure
      @*/
    public static boolean isCheck(Color color, Board board) {
        return isThreatenedBy(color.opponent(), findKing(color, board), board);
    }

    /*@ requires color != null && ctxMoves != null && board != null;
      @ ensures \result <==> isCheck(color, board) && legalMoves(color, ctxMoves, board).isEmpty();
      @ pure
      @*/
    public static boolean isCheckMate(Color color, List<Move> ctxMoves, Board board) {
        return isCheck(color, board) && legalMoves(color, ctxMoves, board).isEmpty();
    }

    /*@ requires color != null && ctxMoves != null && board != null;
      @ ensures \result <==> !isCheck(color, board) && legalMoves(color, ctxMoves, board).isEmpty();
      @ pure
      @*/
    public static boolean isStaleMate(Color color, List<Move> ctxMoves, Board board) {
        return !isCheck(color, board) && legalMoves(color, ctxMoves, board).isEmpty();
    }

    /*@ requires color != null && square != null && board != null;
      @ ensures \result <==> (
      @   \exists Move m;
      @    m != null &&
      @    m.theBoard == board &&
      @    m.theSourcePiece == board.at(m.source) &&
      @    m.theSourcePiece.type.generator.isMoveCorrect(color, board, m);
      @    m.dst.equals(square)
      @ );
      @ pure
      @*/
    public static boolean isThreatenedBy(Color color, Square square, Board board) {
        List<Move> moves = semiLegalMoves(color, board);

        /*@ assert \forall Move m;
          @         m != null &&
          @         m.theBoard == board &&
          @         m.theSourcePiece == board.at(m.source) &&
          @         m.theSourcePiece.type.generator.isMoveCorrect(color, board, m); (
          @           \exists int i; 0 <= i < moves.size(); moves.get(i).equals(m.source, m.dst)
          @         );
          @ assert (
          @          \exists Move m;
          @          m != null &&
          @          m.theBoard == board &&
          @          m.theSourcePiece == board.at(m.source) &&
          @          m.theSourcePiece.type.generator.isMoveCorrect(color, board, m);
          @          m.dst.equals(square)
          @        ) ==> \exists int i; 0 <= i < moves.size(); moves.get(i).dst.equals(square);
          @ assume \exists int i; 0 <= i < moves.size(); moves.get(i).dst.equals(square) <==> (
          @          \exists Move m;
          @          m != null &&
          @          m.theBoard == board &&
          @          m.theSourcePiece == board.at(m.source) &&
          @          m.theSourcePiece.type.generator.isMoveCorrect(color, board, m);
          @          m.dst.equals(square)
          @        );
          @ assert \exists int i; 0 <= i < moves.size(); moves.get(i).dst.equals(square) <==> (
          @          \exists Move m;
          @          m != null &&
          @          m.theBoard == board &&
          @          m.theSourcePiece == board.at(m.source) &&
          @          m.theSourcePiece.type.generator.isMoveCorrect(color, board, m);
          @          m.dst.equals(square)
          @        );
          @*/

        boolean result = moves.stream().anyMatch((move) -> (move.getDst().equals(square)));

        /*@ assert result <==>
          @        \exists int i; 0 <= i < moves.size(); moves.get(i).dst.equals(square);
          @ assert result <==> (
          @          \exists Move m;
          @          m != null &&
          @          m.theBoard == board &&
          @          m.theSourcePiece == board.at(m.source) &&
          @          m.theSourcePiece.type.generator.isMoveCorrect(color, board, m);
          @          m.dst.equals(square)
          @        );
          @*/

        return result;
    }

    /*@ requires color != null && ctxMoves != null && board != null;
      @ ensures \result != null;
      @ ensures \forall int i; 0 <= i < \result.size(); (
      @            \result.get(i) != null &&
      @            \result.get(i).theBoard == board &&
      @            \result.get(i).theSourcePiece == board.at(\result.get(i).source) &&
      @            \result.get(i).theSourcePiece.type.generator.isMoveCorrect(color, board, \result.get(i))
      @          );
      @ ensures \forall Move m;
      @         m != null &&
      @         m.theBoard == board &&
      @         m.theSourcePiece == board.at(m.source) &&
      @         m.theSourcePiece.type.generator.isMoveCorrect(color, board, m); (
      @           \exists int i; 0 <= i < \result.size(); \result.get(i).equals(m.source, m.dst)
      @         );
      @*/
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
      @            \result.get(i).theBoard == board &&
      @            \result.get(i).theSourcePiece == board.at(\result.get(i).source) &&
      @            \result.get(i).theSourcePiece.type.generator.isMoveCorrect(color, board, \result.get(i))
      @          );
      @ ensures \forall Move m;
      @         m != null &&
      @         m.theBoard == board &&
      @         m.theSourcePiece == board.at(m.source) &&
      @         m.theSourcePiece.type.generator.isMoveCorrect(color, board, m); (
      @           \exists int i; 0 <= i < \result.size(); \result.get(i).equals(m.source, m.dst)
      @         );
      @ pure
      @*/
    private static List<Move> semiLegalMoves(Color color, Board board) {
        List<Move> moveList = new ArrayList<>();

        List<Square> squares = board.allSquares();

        /*@ loop_invariant 0 <= i <= squares.size();
          @ loop_invariant \forall int j; 0 <= j < moveList.size(); (
          @                  moveList.get(j) != null &&
          @                  moveList.get(j).theBoard == board &&
          @                  moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
          @                  moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
          @                );
          @ loop_writes moveList.values;
          @ decreases squares.size() - i;
          @*/
        for (int i = 0; i < squares.size(); i++) {
            Square square = squares.get(i);

            Piece piece = board.at(square);

            /*@ assert \forall int j; 0 <= j < moveList.size(); (
              @           moveList.get(j) != null &&
              @           moveList.get(j).theBoard == board &&
              @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
              @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
              @        );
              @*/

            if (piece != null && square.isValid() && piece.isColor(color)) {
                List<Move> moves = piece.availableMoves(square, board);

                //@ assert moveList != moves;

                /*@ assert \forall int j; 0 <= j < moves.size(); (
                  @          moves.get(j) != null &&
                  @          moves.get(j).source == square &&
                  @          moves.get(j).theBoard == board &&
                  @          moves.get(j).theSourcePiece == board.at(moves.get(j).source) &&
                  @          moves.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moves.get(j))
                  @        );
                  @*/

                //@ ghost int initialSize = moveList.size();

                /*@ loop_invariant moveList != moves;
                  @ loop_invariant 0 <= j <= moves.size();
                  @ loop_invariant moveList.size() == initialSize + j;
                  @ loop_invariant \forall int k; initialSize <= k < moveList.size(); (
                  @                  moveList.get(k) == moves.get(k - initialSize)
                  @                );
                  @ loop_writes moveList.values;
                  @ decreases moves.size() - j;
                  @*/
                for (int j = 0; j < moves.size(); j++) {
                    //@ ghost int oldSize = moveList.size();

                    moveList.add(moves.get(j));

                    /*@ assert moveList.size() == oldSize + 1;
                      @ assume \forall int k; initialSize <= k < oldSize; (
                      @          moveList.get(k) == moves.get(k - initialSize)
                      @        );
                      @ assert moveList.get(oldSize) == moves.get(j);
                      @ assert \forall int k; initialSize <= k < oldSize + 1; (
                      @          moveList.get(k) == moves.get(k - initialSize)
                      @        );
                      @ assert \forall int k; initialSize <= k < moveList.size(); (
                      @          moveList.get(k) == moves.get(k - initialSize)
                      @        );
                      @*/
                }

                /*@ assert \forall int j; initialSize <= j < moveList.size(); (
                  @           moveList.get(j) == moves.get(j - initialSize)
                  @        );
                  @ assume \forall int j; 0 <= j < moves.size(); (
                  @           moves.get(j) != null &&
                  @           moves.get(j).theBoard == board &&
                  @           moves.get(j).theSourcePiece == board.at(moves.get(j).source) &&
                  @           moves.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moves.get(j))
                  @        );
                  @ assume \forall int j; 0 <= j < initialSize; (
                  @           moveList.get(j) != null &&
                  @           moveList.get(j).theBoard == board &&
                  @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
                  @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
                  @        );
                  @ assert \forall int j; initialSize <= j < moveList.size(); (
                  @           moveList.get(j) != null &&
                  @           moveList.get(j).theBoard == board &&
                  @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
                  @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
                  @        );
                  @ assert \forall int j; 0 <= j < moveList.size(); (
                  @           moveList.get(j) != null &&
                  @           moveList.get(j).theBoard == board &&
                  @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
                  @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
                  @        );
                  @*/
            } else {
                /*@ assert \forall int j; 0 <= j < moveList.size(); (
                  @           moveList.get(j) != null &&
                  @           moveList.get(j).theBoard == board &&
                  @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
                  @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
                  @        );
                  @*/
            }

            /*@ assume (piece != null && square.isValid() && piece.isColor(color)) ==> \forall int j; 0 <= j < moveList.size(); (
              @           moveList.get(j) != null &&
              @           moveList.get(j).theBoard == board &&
              @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
              @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
              @        );
              @ assume (piece == null || !square.isValid() || !piece.isColor(color)) ==> \forall int j; 0 <= j < moveList.size(); (
              @           moveList.get(j) != null &&
              @           moveList.get(j).theBoard == board &&
              @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
              @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
              @        );
              @ assert \forall int j; 0 <= j < moveList.size(); (
              @           moveList.get(j) != null &&
              @           moveList.get(j).theBoard == board &&
              @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
              @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
              @        );
              @*/
        }

        /*@ assert \forall int j; 0 <= j < moveList.size(); (
          @          moveList.get(j) != null &&
          @          moveList.get(j).theBoard == board &&
          @          moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
          @          moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
          @        );
          @ assume \forall Move m;
          @         m != null &&
          @         m.theBoard == board &&
          @         m.theSourcePiece == board.at(m.source) &&
          @         m.theSourcePiece.type.generator.isMoveCorrect(color, board, m); (
          @           \exists int i; 0 <= i < moveList.size(); moveList.get(i).equals(m.source, m.dst)
          @         );
          @*/

        return moveList;
    }
}
