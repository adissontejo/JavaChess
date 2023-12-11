package com.javachess.state;

import static com.javachess.evaluator.BoardEvaluator.isCheck;
import static com.javachess.evaluator.BoardEvaluator.isCheckMate;
import static com.javachess.evaluator.BoardEvaluator.isStaleMate;

import java.util.ArrayList;
import java.util.List;

import com.javachess.board.Board;
import com.javachess.move.Move;
import com.javachess.piece.Color;

public class GameState {

    private Color playerColor;

    private BoardState boardState;
    private final EnPassantState enPassantState;
    private final CastlingState castlingState;

    /*@ ensures playerColor == Color.WHITE;
      @ ensures boardState == BoardState.STANDARD;
      @ ensures enPassantState != null;
      @ ensures castlingState != null;
      @ ensures \fresh(enPassantState);
      @ ensures \fresh(castlingState);
      @ pure
      @*/
    public GameState() {
        playerColor = Color.WHITE;
        boardState = BoardState.STANDARD;
        enPassantState = new EnPassantState();
        castlingState = new CastlingState();
    }

    /*@ requires playerColor != null && state != null && eps != null && cs != null;
      @ ensures this.playerColor == playerColor;
      @ ensures this.boardState == state;
      @ pure
      @*/
    private GameState(Color playerColor, BoardState state, EnPassantState eps, CastlingState cs) {
        this.playerColor = playerColor;
        this.boardState = state;
        this.enPassantState = eps.copy();
        this.castlingState = cs.copy();
    }

    /*@ ensures \result != null;
      @ ensures \result != this;
      @ ensures \result.playerColor == playerColor;
      @ ensures \result.boardState == boardState;
      @ pure
      @*/
    public GameState copy() {
        return new GameState(playerColor, boardState, enPassantState, castlingState);
    }

    /*@ ensures \result <==> boardState == BoardState.CHECKMATE || boardState == BoardState.STALEMATE;
      @*/
    public boolean isEnded() {
        return boardState == BoardState.CHECKMATE || boardState == BoardState.STALEMATE;
    }

    public void notifyMove(Move move, Board board) {
        playerColor = playerColor.opponent();

        enPassantState.notifyMove(move, board);
        castlingState.notifyMove(move, board);

        evaluateBoardState(board);
    }

    public List<Move> specialMoves() {
        List<Move> moves = new ArrayList<>();

        moves.addAll(enPassantState.getSpecialMoves());
        moves.addAll(castlingState.getSpecialMoves());

        return moves;
    }

    public Color currentPlayerColor() {
        return playerColor;
    }

    private void evaluateBoardState(Board board) {
        boardState = BoardState.STANDARD;

        if (isCheck(playerColor, board)) {
            boardState = BoardState.CHECK;
        }

        if (isCheckMate(playerColor, specialMoves(), board)) {
            boardState = BoardState.CHECKMATE;
        }

        if (isStaleMate(playerColor, specialMoves(), board)) {
            boardState = BoardState.STALEMATE;
        }
    }
}
