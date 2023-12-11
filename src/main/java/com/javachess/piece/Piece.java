package com.javachess.piece;

import java.util.List;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.move.Move;

public enum Piece {

    WHITE_KING(PieceType.KING, Color.WHITE),
    WHITE_QUEEN(PieceType.QUEEN, Color.WHITE),
    WHITE_BISHOP(PieceType.BISHOP, Color.WHITE),
    WHITE_KNIGHT(PieceType.KNIGHT, Color.WHITE),
    WHITE_ROOK(PieceType.ROOK, Color.WHITE),
    WHITE_PAWN(PieceType.PAWN, Color.WHITE),
    BLACK_KING(PieceType.KING, Color.BLACK),
    BLACK_QUEEN(PieceType.QUEEN, Color.BLACK),
    BLACK_BISHOP(PieceType.BISHOP, Color.BLACK),
    BLACK_KNIGHT(PieceType.KNIGHT, Color.BLACK),
    BLACK_ROOK(PieceType.ROOK, Color.BLACK),
    BLACK_PAWN(PieceType.PAWN, Color.BLACK);

    //@ spec_public
    private final PieceType type;
    //@ spec_public
    private final Color color;

    //@ axiom \forall Piece piece; ; piece.type != null && piece.color != null;

    /*@ requires type != null && color != null;
      @ ensures this.type == type;
      @ ensures this.color == color;
      @ pure
      @*/
    Piece(PieceType type, Color color) {
        this.type = type;
        this.color = color;
    }

    /*@ ensures \result == color;
      @ pure
      @*/
    public Color color() {
        return color;
    }

    /*@ ensures \result == type;
      @ pure
      @*/
    public PieceType type() {
        return type;
    }

    /*@ public normal_behavior
      @ ensures \result == (color == otherColor);
      @ pure
      @*/
    public boolean isColor(Color otherColor) {
        return color == otherColor;
    }

    /*@ public normal_behavior
      @ ensures \result == (type == otherType);
      @ pure
      @*/
    public boolean isType(PieceType otherType) {
        return type == otherType;
    }

    /*@ requires position != null && board != null;
      @ requires position.isValid();
      @ requires board.at(position) == this;
      @ ensures \result != null;
      @ ensures \forall int i; 0 <= i < \result.size(); (
      @   \result.get(i) != null &&
      @   \result.get(i).source == position &&
      @   \result.get(i).theBoard == board &&
      @   \result.get(i).theSourcePiece == this &&
      @   type.generator.isMoveCorrect(color, board, \result.get(i))
      @ );
      @ ensures \forall Move m; m != null && m.source == position && m.theBoard == board && m.theSourcePiece == this && type.generator.isMoveCorrect(color, board, m); (
      @           \exists int i; 0 <= i < \result.size(); \result.get(i).equals(m.source, m.dst)
      @         );
      @ ensures \fresh(\result);
      @ pure
      @*/
    public List<Move> availableMoves(Square position, Board board) {
        List<Move> moves = type.generator().generateMoves(position, color, board);

        return type.generator().generateMoves(position, color, board);
    }
}
