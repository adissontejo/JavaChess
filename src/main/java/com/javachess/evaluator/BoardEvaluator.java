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
      @ ensures \result <==> (
      @           \exists Move m;
      @            m != null &&
      @            m.theBoard == board &&
      @            m.theSourcePiece == board.at(m.source) &&
      @            m.theSourcePiece.color == color.opponent() &&
      @            m.theSourcePiece.type.generator.isMoveCorrect(color, board, m);
      @            board.at(m.dst) != null &&
      @            board.at(m.dst).isColor(color) &&
      @            board.at(m.dst).isType(PieceType.KING)
      @         );
      @ pure
      @*/
    public static boolean isCheck(Color color, Board board) {
        Square king = findKing(color, board);

        boolean result = isThreatenedBy(color.opponent(), king, board);

        /*@ assume result <==> (
          @          \exists Move m;
          @           m != null &&
          @           m.theBoard == board &&
          @           m.theSourcePiece == board.at(m.source) &&
          @           m.theSourcePiece.color == color.opponent() &&
          @           m.theSourcePiece.type.generator.isMoveCorrect(color, board, m);
          @           board.at(m.dst) != null &&
          @           board.at(m.dst).isColor(color) &&
          @           board.at(m.dst).isType(PieceType.KING)
          @        );
          @*/

        return result;
    }

    public static boolean isCheckMate(Color color, List<Move> ctxMoves, Board board) {
        return isCheck(color, board) && legalMoves(color, ctxMoves, board).isEmpty();
    }

    public static boolean isStaleMate(Color color, List<Move> ctxMoves, Board board) {
        return !isCheck(color, board) && legalMoves(color, ctxMoves, board).isEmpty();
    }

    /*@ requires color != null && square != null && board != null;
      @ ensures \result <==> (
      @           \exists Move m;
      @            m != null &&
      @            m.theBoard == board &&
      @            m.theSourcePiece == board.at(m.source) &&
      @            m.theSourcePiece.type.generator.isMoveCorrect(color, board, m);
      @            m.dst.equals(square)
      @         );
      @ pure
      @*/
    public static boolean isThreatenedBy(Color color, Square square, Board board) {
        List<Move> moves = semiLegalMoves(color, board);

        boolean result = moves.stream().anyMatch((move) -> (move.getDst().equals(square)));

        /*@ assume result <==> (
          @          \exists Move m;
          @           m != null &&
          @           m.theBoard == board &&
          @           m.theSourcePiece == board.at(m.source) &&
          @           m.theSourcePiece.type.generator.isMoveCorrect(color, board, m);
          @           m.dst.equals(square)
          @        );
          @*/

        return result;
    }

    public static List<Move> legalMoves(Color color, List<Move> ctxMoves, Board board) {
        List<Move> legalMoves = new ArrayList<>();
        List<Move> semiLegalMoves = semiLegalMoves(color, board);

        if (ctxMoves != null) {
            semiLegalMoves.addAll(ctxMoves);
        }

        for (Move move : semiLegalMoves) {

            Move moveCopy = move.copy();

            moveCopy.execute();

            if (!isCheck(color, moveCopy.getBoard())) {
                legalMoves.add(move);
            }

            move.undo();
        }

        return legalMoves;
    }

    /*@   public normal_behavior
      @   requires color != null && board != null;
      @   requires \exists int k, l; 0 <= k < 8 && 0 <= l < 8; (
      @              board.at(Square.at(k, l)) != null &&
      @              board.at(Square.at(k, l)).isColor(color) &&
      @              board.at(Square.at(k, l)).isType(PieceType.KING)
      @            );
      @   ensures \result != null;
      @   ensures \result.isValid();
      @   ensures board.at(\result) != null;
      @   ensures board.at(\result).isType(PieceType.KING);
      @   ensures board.at(\result).isColor(color);
      @ also
      @   public exceptional_behavior
      @   requires color != null && board != null;
      @   requires !\exists int k, l; 0 <= k < 8 && 0 <= l < 8; (
      @              board.at(Square.at(k, l)) != null &&
      @              board.at(Square.at(k, l)).isColor(color) &&
      @              board.at(Square.at(k, l)).isType(PieceType.KING)
      @            );
      @   signals_only IllegalStateException;
      @ pure
      @*/
    public static Square findKing(Color color, Board board) {
        /*@ loop_invariant 0 <= i <= 8;
          @ loop_invariant \forall int k, l; 0 <= k < i && 0 <= l < 8; (
          @                  board.at(Square.at(k, l)) == null ||
          @                  !board.at(Square.at(k, l)).isColor(color) ||
          @                  !board.at(Square.at(k, l)).isType(PieceType.KING)
          @                );
          @ loop_writes i;
          @ decreases 8 - i;
          @*/
        for (int i = 0; i < 8; i++) {
            /*@ loop_invariant 0 <= j <= 8;
              @ loop_invariant \forall int l; 0 <= l < j; (
              @                  board.at(Square.at(i, l)) == null ||
              @                  !board.at(Square.at(i, l)).isColor(color) ||
              @                  !board.at(Square.at(i, l)).isType(PieceType.KING)
              @                );
              @ loop_writes j;
              @ decreases 8 - j;
              @*/
            for (int j = 0; j < 8; j++) {
                Square square = Square.at(i, j);

                Piece piece = board.at(square);

                if (piece != null && piece.isColor(color) && piece.isType(PieceType.KING)) {
                    /*@ assert board.at(Square.at(i, j)) != null &&
                      @        board.at(Square.at(i, j)).isColor(color) &&
                      @        board.at(Square.at(i, j)).isType(PieceType.KING);
                      @ assume \exists int k, l; 0 <= k < 8 && 0 <= l < 8; (
                      @          board.at(Square.at(k, l)) != null &&
                      @          board.at(Square.at(k, l)).isColor(color) &&
                      @          board.at(Square.at(k, l)).isType(PieceType.KING)
                      @        );
                      @*/
                    return square;
                }

                /*@ assert \forall int l; 0 <= l < j; (
                  @          board.at(Square.at(i, l)) == null ||
                  @          !board.at(Square.at(i, l)).isColor(color) ||
                  @          !board.at(Square.at(i, l)).isType(PieceType.KING)
                  @        );
                  @ assert board.at(Square.at(i, j)) == null ||
                  @        !board.at(Square.at(i, j)).isColor(color) ||
                  @        !board.at(Square.at(i, j)).isType(PieceType.KING);
                  @ assume \forall int l; 0 <= l < j + 1; (
                  @          board.at(Square.at(i, l)) == null ||
                  @          !board.at(Square.at(i, l)).isColor(color) ||
                  @          !board.at(Square.at(i, l)).isType(PieceType.KING)
                  @        );
                  @*/
            }

            /*@ assert \forall int k, l; 0 <= k < i && 0 <= l < 8; (
              @          board.at(Square.at(k, l)) == null ||
              @          !board.at(Square.at(k, l)).isColor(color) ||
              @          !board.at(Square.at(k, l)).isType(PieceType.KING)
              @        );
              @ assert \forall int l; 0 <= l < 8; (
              @          board.at(Square.at(i, l)) == null ||
              @          !board.at(Square.at(i, l)).isColor(color) ||
              @          !board.at(Square.at(i, l)).isType(PieceType.KING)
              @        );
              @ assert \forall int k, l; 0 <= k < i + 1 && 0 <= l < 8; (
              @          board.at(Square.at(k, l)) == null ||
              @          !board.at(Square.at(k, l)).isColor(color) ||
              @          !board.at(Square.at(k, l)).isType(PieceType.KING)
              @        );
              @*/
        }

        /*@ assert \forall int k, l; 0 <= k < 8 && 0 <= l < 8; (
          @          board.at(Square.at(k, l)) == null ||
          @          !board.at(Square.at(k, l)).isColor(color) ||
          @          !board.at(Square.at(k, l)).isType(PieceType.KING)
          @        );
          @ assert !\exists int k, l; 0 <= k < 8 && 0 <= l < 8; (
          @          board.at(Square.at(k, l)) != null &&
          @          board.at(Square.at(k, l)).isColor(color) &&
          @          board.at(Square.at(k, l)).isType(PieceType.KING)
          @        );
          @*/

        throw new IllegalStateException("The king is missing!");
    }

    /*@ requires color != null && board != null;
      @ ensures \result != null;
      @ ensures \forall int i; 0 <= i < \result.size(); (
      @            \result.get(i) != null &&
      @            \result.get(i).theBoard == board &&
      @            \result.get(i).theSourcePiece == board.at(\result.get(i).source) &&
      @            \result.get(i).theSourcePiece.color == color &&
      @            \result.get(i).theSourcePiece.type.generator.isMoveCorrect(color, board, \result.get(i))
      @          );
      @ ensures \forall Move m;
      @         m != null &&
      @         m.theBoard == board &&
      @         m.theSourcePiece == board.at(m.source) &&
      @         m.theSourcePiece.color == color &&
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
          @                  moveList.get(j).theSourcePiece.color == color &&
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
              @           moveList.get(j).theSourcePiece.color == color &&
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
                  @          moves.get(j).theSourcePiece.color == color &&
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
                  @           moves.get(j).theSourcePiece.color == color &&
                  @           moves.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moves.get(j))
                  @        );
                  @ assume \forall int j; 0 <= j < initialSize; (
                  @           moveList.get(j) != null &&
                  @           moveList.get(j).theBoard == board &&
                  @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
                  @           moveList.get(j).theSourcePiece.color == color &&
                  @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
                  @        );
                  @ assert \forall int j; initialSize <= j < moveList.size(); (
                  @           moveList.get(j) != null &&
                  @           moveList.get(j).theBoard == board &&
                  @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
                  @           moveList.get(j).theSourcePiece.color == color &&
                  @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
                  @        );
                  @ assert \forall int j; 0 <= j < moveList.size(); (
                  @           moveList.get(j) != null &&
                  @           moveList.get(j).theBoard == board &&
                  @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
                  @           moveList.get(j).theSourcePiece.color == color &&
                  @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
                  @        );
                  @*/
            } else {
                /*@ assert \forall int j; 0 <= j < moveList.size(); (
                  @           moveList.get(j) != null &&
                  @           moveList.get(j).theBoard == board &&
                  @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
                  @           moveList.get(j).theSourcePiece.color == color &&
                  @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
                  @        );
                  @*/
            }

            /*@ assume (piece != null && square.isValid() && piece.isColor(color)) ==> \forall int j; 0 <= j < moveList.size(); (
              @           moveList.get(j) != null &&
              @           moveList.get(j).theBoard == board &&
              @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
              @           moveList.get(j).theSourcePiece.color == color &&
              @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
              @        );
              @ assume (piece == null || !square.isValid() || !piece.isColor(color)) ==> \forall int j; 0 <= j < moveList.size(); (
              @           moveList.get(j) != null &&
              @           moveList.get(j).theBoard == board &&
              @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
              @           moveList.get(j).theSourcePiece.color == color &&
              @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
              @        );
              @ assert \forall int j; 0 <= j < moveList.size(); (
              @           moveList.get(j) != null &&
              @           moveList.get(j).theBoard == board &&
              @           moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
              @           moveList.get(j).theSourcePiece.color == color &&
              @           moveList.get(j).theSourcePiece.type.generator.isMoveCorrect(color, board, moveList.get(j))
              @        );
              @*/
        }

        /*@ assert \forall int j; 0 <= j < moveList.size(); (
          @          moveList.get(j) != null &&
          @          moveList.get(j).theBoard == board &&
          @          moveList.get(j).theSourcePiece == board.at(moveList.get(j).source) &&
          @          moveList.get(j).theSourcePiece.color == color &&
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
