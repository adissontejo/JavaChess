package com.javachess.logger;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.piece.Color;
import com.javachess.piece.Piece;
import com.javachess.piece.PieceType;

public class Logger {
    public static void logBoard(Board board) {
        for (int row = 7; row >= 0; row--) {
            for (int col = 0; col < 8; col++) {
                Piece piece = board.at(Square.at(row, col));

                if (piece == null) {
                    System.out.print("-- ");

                    continue;
                }

                if (piece.isColor(Color.WHITE)) {
                    System.out.print("w");
                } else {
                    System.out.print("b");
                }

                if (piece.isType(PieceType.KING)) {
                    System.out.print("K ");
                } else if (piece.isType(PieceType.QUEEN)) {
                    System.out.print("Q ");
                } else if (piece.isType(PieceType.BISHOP)) {
                    System.out.print("B ");
                } else if (piece.isType(PieceType.KNIGHT)) {
                    System.out.print("N ");
                } else if (piece.isType(PieceType.ROOK)) {
                    System.out.print("R ");
                } else if (piece.isType(PieceType.PAWN)) {
                    System.out.print("P ");
                }
            }

            System.out.println();
        }
    }
}
