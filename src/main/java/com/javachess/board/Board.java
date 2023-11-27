package com.javachess.board;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.javachess.piece.Color;
import com.javachess.piece.Piece;

/**
 * Chess board representation
 *
 * @author Ouzned
 *
 */
public class Board {
    //@ spec_public
    private final Map<Square, Piece> positions;

    //@ invariant positions != null;

    //@ ensures positions instanceof HashMap<Square, Piece>;
    //@ pure
    public Board() {
        positions = new HashMap<Square, Piece>();
    }

    //@ requires newBoard != null;
    //@ ensures positions == newBoard;
    //@ ensures \forall Square s; ; \old(newBoard.get(s)) == newBoard.get(s);
    //@ pure
    private Board(Map<Square, Piece> newBoard) {
        this.positions = newBoard;
    }

    //@ ensures \forall Square s; ; at(s) == \result.at(s);
    //@ pure
    public Board copy() {
        Map<Square, Piece> map = new HashMap<Square, Piece>(positions);
        
        //@ assert \forall Square s; ; map.get(s) == positions.get(s);

        Board board = new Board(map);

        return board;
    }

    //@ pure
    public List<Square> allSquares() {
        return new ArrayList<Square>(positions.keySet());
    }

    //@ ensures \result == positions.get(square);
    //@ pure
    public Piece at(Square square) {
        return positions.get(square);
    }

    public void removePieceAt(Square square) {
        positions.remove(square);
    }

    public void setPieceAt(Square position, Piece piece) {
        if (position != null && piece != null) {
            positions.put(position, piece);
        }
    }

    public void movePiece(Square src, Square dst) {
        Piece piece = at(src);

        removePieceAt(src);
        setPieceAt(dst, piece);
    }

    //@  requires square != null;
    //@  ensures \result == !positions.containsKey(square);
    //@ also
    //@  requires square == null;
    //@  ensures \result == false;
    //@ pure
    public boolean isFree(Square square) {
        if (square == null) {
            return false;
        }

        return !positions.containsKey(square);
    }

    //@  requires at(square) != null;
    //@  ensures \result == (at(square).color() == color);
    //@ also
    //@  requires at(square) == null;
    //@  ensures \result == false;
    //@ pure
    public boolean isColor(Square square, Color color) {
        Piece piece = at(square);

        if (piece != null) {
            return piece.color() == color;
        }

        return false;
    }
}
