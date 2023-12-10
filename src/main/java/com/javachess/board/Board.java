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

    //@ public invariant positions != null;

    /*@ ensures positions instanceof HashMap<Square, Piece>;
      @ pure
      @*/
    public Board() {
        positions = new HashMap<Square, Piece>();
    }

    /*@ requires newBoard != null;
      @ ensures positions == newBoard;
      @ ensures \forall Square s; ; \old(newBoard.get(s)) == newBoard.get(s);
      @ pure
      @*/
    private Board(Map<Square, Piece> newBoard) {
        this.positions = newBoard;
    }

    /*@ ensures \forall Square s; ; at(s) == \result.at(s);
      @ ensures \forall Square s; ; positions.get(s) == \old(positions.get(s));
      @ pure
      @*/
    public Board copy() {
        Map<Square, Piece> map = new HashMap<Square, Piece>(positions);

        //@ assert \forall Square s; ; map.get(s) == positions.get(s);

        Board board = new Board(map);

        return board;
    }

    /*@ ensures \result instanceof ArrayList<Square>;
      @ ensures \forall Square s; ; \result.contains(s) <==> positions.containsKey(s);
      @ pure
      @*/
    public List<Square> allSquares() {
        List<Square> squares = new ArrayList<>(positions.keySet());

        //@ assert \forall Square s; ; squares.contains(s) <==> positions.keySet().contains(s);
        //@ assert \forall Square s; ; positions.keySet().contains(s) <==> positions.containsKey(s);

        return squares;
    }

    /*@   requires square != null;
      @   ensures \result == positions.get(square);
      @ also
      @   requires square == null;
      @   ensures \result == null;
      @ pure
      @*/
    public Piece at(Square square) {
        if (square == null) {
            return null;
        }

        return positions.get(square);
    }

    /*@   requires square != null;
      @   ensures !positions.containsKey(square);
      @   ensures \forall Square s; s != square ; at(s) == \old(at(s));
      @   ensures \forall Square s; s != square ;
      @           positions.containsKey(s) == \old(positions.containsKey(s));
      @   assignable positions.objectState;
      @ also
      @   requires square == null;
      @   assignable \nothing;
      @*/
    public void removePieceAt(Square square) {
        if (square == null) {
            return;
        }

        positions.remove(square);
    }

    /*@   requires position != null && piece != null;
      @   ensures at(position) == piece;
      @   ensures \forall Square s; s != position ; at(s) == \old(at(s));
      @   ensures \forall Square s; s != position ;
      @          positions.containsKey(s) == \old(positions.containsKey(s));
      @   assignable positions.objectState;
      @ also
      @   requires position == null || piece == null;
      @   assignable \nothing;
      @*/
    public void setPieceAt(Square position, Piece piece) {
        if (position == null || piece == null) {
            return;
        }

        positions.put(position, piece);
    }

    /*@   requires src != null && dst != null && at(src) != null;
      @   ensures src != dst ==> !positions.containsKey(src);
      @   ensures at(dst) == \old(at(src));
      @   ensures \forall Square s; s != src && s != dst ; at(s) == \old(at(s));
      @   ensures \forall Square s; s != src && s != dst ;
      @            positions.containsKey(s) == \old(positions.containsKey(s));
      @   assignable positions.objectState;
      @ also
      @   requires src == null || dst == null || at(src) == null;
      @   assignable \nothing;
      @*/
    public void movePiece(Square src, Square dst) {
        Piece piece = at(src);

        if (src == null || dst == null || piece == null) {
            return;
        }

        removePieceAt(src);
        setPieceAt(dst, piece);
    }

    /*@   requires square != null;
      @   ensures \result == !positions.containsKey(square);
      @ also
      @   requires square == null;
      @   ensures \result == false;
      @ pure
      @*/
    public boolean isFree(Square square) {
        if (square == null) {
            return false;
        }

        return !positions.containsKey(square);
    }

    /*@   requires at(square) != null;
      @   ensures \result == (at(square).color() == color);
      @ also
      @   requires at(square) == null;
      @   ensures \result == false;
      @ pure
      @*/
    public boolean isColor(Square square, Color color) {
        Piece piece = at(square);

        if (piece != null) {
            return piece.color() == color;
        }

        return false;
    }
}
