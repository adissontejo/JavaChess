package com.javachess.game;

import static com.javachess.evaluator.BoardEvaluator.legalMoves;
import static com.javachess.logger.Logger.logBoard;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import com.javachess.board.Board;
import com.javachess.board.Square;
import com.javachess.board.initializer.BoardInitializer;
import com.javachess.converter.NotationConverter;
import com.javachess.move.Move;
import com.javachess.piece.Color;
import com.javachess.player.Player;
import com.javachess.state.GameState;

public class Game {

    //@ spec_public
    private GameState state;
    //@ spec_public
    private final Board board;
    //@ spec_public
    private final NotationConverter converter;

    //@ spec_public
    private final Stack<Move> moveHistory;
    //@ spec_public
    private final Stack<GameState> stateHistory;
    //@ spec_public
    private final Map<Color, Player> players;

    //@ requires player1 != null && player2 != null && converter != null && initializer != null;
    //@ ensures board != null && this.converter == converter && this.state != null && moveHistory != null &&
    //@     stateHistory != null && players != null && players.get(Color.WHITE) == player1 &&
    //@     players.get(Color.BLACK) == player2;
    public Game(Player player1, Player player2, NotationConverter converter, BoardInitializer initializer) {
        this.board = new Board();
        this.converter = converter;
        this.state = new GameState();

        moveHistory = new Stack<>();
        stateHistory = new Stack<>();

        players = new HashMap<>();
        players.put(Color.WHITE, player1);
        players.put(Color.BLACK, player2);

        initializer.init(board);
    }

    public void start() {
        while (!state.isEnded()) {
            logBoard(board);

            String notation = players.get(state.currentPlayerColor()).takeMove(this);

            Square srcSquare = converter.getSrc(notation);
            Square dstSquare = converter.getDst(notation);

            List<Move> legalMoves = legalMoves(state.currentPlayerColor(), state.specialMoves(), board);

            for (Move move : legalMoves) {
                if (move.equals(srcSquare, dstSquare)) {
                    executeMove(move);
                    break;
                }
            }
        }
    }



    /*@ requires !moveHistory.isEmpty() && !stateHistory.isEmpty();
      @ ensures \old(moveHistory.size()) == moveHistory.size() + 1;
      @ ensures \old(stateHistory.size()) == stateHistory.size() + 1;
      @ ensures (\forall int i; 0 <= i && i < moveHistory.size(); \old(moveHistory.get(i)) == moveHistory.get(i));
      @ ensures (\forall int i; 0 <= i && i < stateHistory.size(); \old(stateHistory.get(i)) == stateHistory.get(i));
      @ ensures \old(state) != state;
      @*/
    public void undo() {
        moveHistory.peek().undo();
        moveHistory.pop();

        state = stateHistory.pop();
    }

    /*@ requires move != null;
      @ ensures moveHistory.contains(move);
      @ ensures (\forall int i; 0 <= i < moveHistory.size() - 1; \old(moveHistory.get(i)) == moveHistory.get(i));
      @ ensures moveHistory.get(moveHistory.size() - 1) == move;
      @ ensures (\forall int i; 0 <= i < stateHistory.size() - 1; \old(stateHistory.get(i)) == stateHistory.get(i));
      @ ensures moveHistory.get(moveHistory.size() - 1) == move;
      @ ensures stateHistory.get(stateHistory.size() - 1) == \old(state);
      @*/
    private void executeMove(Move move) {
        move.execute();

        moveHistory.add(move);
        stateHistory.add(state.copy());

        state.notifyMove(move, board);
    }
}
