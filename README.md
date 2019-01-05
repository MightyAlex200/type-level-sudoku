# Type-level Sudoku

This is a Sudoku game implemented in Idris such that the type `Sudoku` is inhabited only by values that represent valid game states.

`Sudoku.idr` is fully documented, so feel free to dissect it.

## Running

`Main.idr` contains a basic, crudely constructed CLI for the game. The `Makefile` will build this CLI and output it as `Sudoku.out` when running `make` from the command line. You will need [Idris](https://www.idris-lang.org/). You can also load either file in the interactive environment by running `idris <file>` at the command-line.

## Why?
N/A