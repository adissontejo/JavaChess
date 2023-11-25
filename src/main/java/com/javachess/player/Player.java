package com.javachess.player;

import java.util.Scanner;

import com.javachess.game.Game;

/**
 * Chess player contract
 *
 * @author Ouzned
 *
 */
public class Player {
    private static final Scanner scanner = new Scanner(System.in);
    /**
     * Prompts the user for the next move. The value returned must be in a chess
     * notation that can be understood by the board's NotationConverter
     *
     * @param game
     * @return the next move encoded in a given chess notation
     */
    public String takeMove(Game game) {
        String move = scanner.nextLine();

        return move;
    }
}
