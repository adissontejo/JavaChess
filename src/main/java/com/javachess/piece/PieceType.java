package com.javachess.piece;

import com.javachess.generator.BishopMoveGenerator;
import com.javachess.generator.KingMoveGenerator;
import com.javachess.generator.KnightMoveGenerator;
import com.javachess.generator.MoveGenerator;
import com.javachess.generator.PawnMoveGenerator;
import com.javachess.generator.QueenMoveGenerator;
import com.javachess.generator.RookMoveGenerator;

public enum PieceType {

    KING(new KingMoveGenerator()),
    QUEEN(new QueenMoveGenerator()),
    BISHOP(new BishopMoveGenerator()),
    KNIGHT(new KnightMoveGenerator()),
    ROOK(new RookMoveGenerator()),
    PAWN(new PawnMoveGenerator());

    //@ spec_public
    private final MoveGenerator generator;

    //@ axiom \forall PieceType type; ; type.generator != null;

    /*@ requires generator != null;
      @ ensures this.generator == generator;
      @ pure
      @*/
    private PieceType(MoveGenerator generator) {
        this.generator = generator;
    }

    /*@ ensures \result == generator;
      @ pure
      @*/
    public MoveGenerator generator() {
        return generator;
    }
}
