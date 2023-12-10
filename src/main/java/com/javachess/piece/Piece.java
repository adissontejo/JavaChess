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

    //@ public invariant type != null;
    //@ public invariant type.generator != null;
    //@ public invariant color != null;

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

    /*@ ensures \result == (color == otherColor);
      @ pure
      @*/
    public boolean isColor(Color otherColor) {
        return color == otherColor;
    }

    /*@ ensures \result == (type == otherType);
      @ pure
      @*/
    public boolean isType(PieceType otherType) {
        return type == otherType;
    }

    /*@ requires position != null && board != null;
      @ requires position.isValid();
      @ ensures \result != null;
      @ ensures \forall int i; 0 <= i < \result.size(); (
      @   \result.get(i) != null &&
      @   \result.get(i).source == position &&
      @   \result.get(i).theBoard == board
      @ );
      @ pure
      @*/
    public List<Move> availableMoves(Square position, Board board) {
        return type.generator.generateMoves(position, color, board);
    }
}
