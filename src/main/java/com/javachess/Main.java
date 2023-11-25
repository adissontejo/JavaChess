package com.javachess;

import com.javachess.game.Game;
import com.javachess.player.Player;
import com.javachess.converter.StandardConverter;
import com.javachess.board.initializer.StandardInitializer;

public class Main {
    public static void main(String[] args) {
        Player white = new Player();
        Player black = new Player();

        StandardConverter converter = new StandardConverter();
        StandardInitializer initializer = new StandardInitializer();


        Game game = new Game(white, black, converter, initializer);

        game.start();
    }
}
