package com.javachess.move.castling;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.evaluator.BoardEvaluator;
import com.javachess.move.Move;
import com.javachess.piece.Color;
import com.javachess.piece.Piece;

public abstract class Castling implements Move {
    //@ spec_public
    protected final Board board; //@ in theBoard;
    //@ spec_public
    protected Square kingSquare; //@ in source;
                                 //@ in dst;
    //@ spec_public
    protected Piece sourcePiece; //@ in theSourcePiece;

    //@ public instance model boolean isKingSide; in dst;

    //@ public represents source = kingSquare;
    //@ public represents dst = (isKingSide ? Square.atOffset(kingSquare, 0, 2) : Square.atOffset(kingSquare, 0, -2));
    //@ public represents theSourcePiece = sourcePiece;
    //@ public represents theCapturedPiece = null;
    //@ public represents theBoard = board;

    /*@ requires color != null && board != null;
      @ ensures theBoard == board;
      @ ensures theSourcePiece == (color == Color.WHITE ? Piece.WHITE_KING : Piece.BLACK_KING);
      @*/
    public Castling(Color color, Board board) {
        /*@ assume \exists int i, j; 0 <= i < 8 && 0 <= j < 8; (
          @          board.at(Square.at(i, j)) != null &&
          @          board.at(Square.at(i, j)).type() == com.javachess.piece.PieceType.KING &&
          @          board.at(Square.at(i, j)).color() == color
          @        );
          @*/

        this.board = board;
        this.kingSquare = BoardEvaluator.findKing(color, board);
        this.sourcePiece = color == Color.WHITE ? Piece.WHITE_KING : Piece.BLACK_KING;
        //@ assume this.kingSquare != null;
        //@ assume this.kingSquare.isValid();
        //@ assume dst != null;
    }

    /*@ also
      @   ensures board.at(kingSquare) == null;
      @   ensures board.at(getDst()) == \old(board.at(kingSquare));
      @   ensures board.at(getRookSrc()) == null;
      @   ensures board.at(getRookDst()) == \old(board.at(getRookSrc()));
      @ pure
      @*/
    @Override
    public void execute() {
        board.movePiece(kingSquare, getDst());
        board.movePiece(getRookSrc(), getRookDst());
    }

    /*@ also
      @   ensures board.at(getDst()) == null;
      @   ensures board.at(kingSquare) == \old(board.at(getDst()));
      @   ensures board.at(getRookDst()) == null;
      @   ensures board.at(getRookSrc()) == \old(board.at(getRookDst()));
      @ pure
      @*/
    @Override
    public void undo() {
        board.movePiece(getDst(), kingSquare);
        board.movePiece(getRookDst(), getRookSrc());
    }

    @Override
    public Piece getSourcePiece() {
        return sourcePiece;
    }

    @Override
    public Piece getCapturedPiece() {
        return null;
    }

    @Override
    public Square getSource() {
        return kingSquare;
    }

    /*@ also
      @   ensures \result != null;
      @   {|
      @      requires isKingSide;
      @      ensures \result.equals(Square.atOffset(kingSquare, 0, 2));
      @   also
      @      requires !isKingSide;
      @      ensures \result.equals(Square.atOffset(kingSquare, 0, -2));
      @   |}
      @ pure
      @*/
    @Override
    public abstract Square getDst();


    /*@ also
      @   ensures \result <==> (
      @             source.equals(src) &&
      @             getDst().equals(dst)
      @           );
      @*/
    @Override
    public boolean equals(Square src, Square dst) {
        return getSource().equals(src) && getDst().equals(dst);
    }

    @Override
    public Board getBoard() {
        return board;
    }

    /*@ ensures \result != null;
      @ {|
      @    requires isKingSide;
      @    ensures \result.equals(Square.atOffset(kingSquare, 0, 3));
      @ also
      @    requires !isKingSide;
      @    ensures \result.equals(Square.atOffset(kingSquare, 0, -4));
      @ |}
      @ pure
      @*/
    protected abstract Square getRookSrc();

    /*@ ensures \result != null;
      @ {|
      @    requires isKingSide;
      @    ensures \result.equals(Square.atOffset(kingSquare, 0, 1));
      @ also
      @    requires !isKingSide;
      @    ensures \result.equals(Square.atOffset(kingSquare, 0, -1));
      @ |}
      @ pure
      @*/
    protected abstract Square getRookDst();
}
