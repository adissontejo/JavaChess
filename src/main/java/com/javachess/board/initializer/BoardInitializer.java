package com.javachess.board.initializer;

import com.javachess.board.Board;

public interface BoardInitializer {
    /*@ requires board != null;
      @ pure
      @*/
    void init(Board board);
}
