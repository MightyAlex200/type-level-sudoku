module Main

%default total

||| A digit in the game of Sudoku.
||| Can be from 1 - 9 inclusive.
||| Used for many things, including:
|||   - As the player's moves
|||   - Indexing the board
|||   - Indexing the board's subsquares
data SudokuDigit : Type where
  One : SudokuDigit
  Two : SudokuDigit
  Three : SudokuDigit
  Four : SudokuDigit
  Five : SudokuDigit
  Six : SudokuDigit
  Seven : SudokuDigit
  Eight : SudokuDigit
  Nine : SudokuDigit

implementation Eq SudokuDigit where
  One == One = True
  Two == Two = True
  Three == Three = True
  Four == Four = True
  Five == Five = True
  Six == Six = True
  Seven == Seven = True
  Eight == Eight = True
  Nine == Nine = True
  _ == _ = False

||| Represents a board position (x, y)
SudokuPosition : Type
SudokuPosition = (SudokuDigit, SudokuDigit)

||| A Sudoku board whose validity is completely unchecked
data UnsafeSudoku : Type where
  ||| An empty Sudoku board
  Empty : UnsafeSudoku
  ||| A Sudoku board that has at least one number on it
  |||
  ||| @ s The state of the board before the current move
  ||| @ p The position of the current move
  ||| @ d The digit of the current move
  Move  : (s : UnsafeSudoku) -> (p : SudokuPosition) -> (d : SudokuDigit) -> UnsafeSudoku

||| Helper function for getting the digit of a position on a Sudoku board
sudokuPosition : UnsafeSudoku -> SudokuPosition -> Maybe SudokuDigit
sudokuPosition Empty p = Nothing
sudokuPosition (Move s ps d) p =
  if p == ps
  then Just d
  else sudokuPosition s p

||| Validate that a list of SudokuDigits contains no duplicates
sudokuDigitsValid : List SudokuDigit -> Bool
sudokuDigitsValid [] = True
sudokuDigitsValid (x :: xs) = (not (x `elem` xs)) && (sudokuDigitsValid xs)

||| A list of all SudokuDigits
digits : List SudokuDigit
digits = [ One,   Two,   Three
         , Four,  Five,  Six
         , Seven, Eight, Nine ]

||| Helper function to get a vertical line on a Sudoku board
|||
||| @ s The Sudoku board to query
||| @ d The x coordinate of the vertical line
sudokuVert : (s : UnsafeSudoku) -> (d : SudokuDigit) -> List SudokuDigit
sudokuVert s d = mapMaybe (sudokuPosition s) positions
  where positions : List SudokuPosition
        positions = map (MkPair d) digits

||| Given an unvalidated Sudoku board, return true
||| if it's vertical lines are valid
sudokuVertsValid : UnsafeSudoku -> Bool
sudokuVertsValid s = all sudokuDigitsValid (map (sudokuVert s) digits)

||| Helper function to get a horizontal line on a Sudoku board
|||
||| @ s The Sudoku board to query
||| @ d The y coordinate of the horizontal line
sudokuHorizontal : (s : UnsafeSudoku) -> (d : SudokuDigit) -> List SudokuDigit
sudokuHorizontal s d = mapMaybe (sudokuPosition s) positions
  where positions : List SudokuPosition
        positions = map (flip MkPair d) digits

||| Given an unvalidated Sudoku board, return true
||| if it's horizontal lines are valid
sudokuHorizontalsValid : UnsafeSudoku -> Bool
sudokuHorizontalsValid s = all sudokuDigitsValid (map (sudokuHorizontal s) digits)

||| Returns the digits of a Sudoku board from the 3x3 square of the given position
|||
||| @ s The Sudoku board to query
||| @ d The digit of the 3x3 square
sudokuSquare : (s : UnsafeSudoku) -> (d : SudokuDigit) -> List SudokuDigit
sudokuSquare s d = mapMaybe (sudokuPosition s) positions
  where ott : List SudokuDigit
        ott = [One, Two, Three]
        ffs : List SudokuDigit
        ffs = [Four, Five, Six]
        sen : List SudokuDigit
        sen = [Seven, Eight, Nine]
        g : List SudokuDigit -> List SudokuDigit -> List SudokuPosition
        g a b =
          concatMap (\ea => map (MkPair ea) b) a
        positions =
          case d of
            One   => g ott ott
            Two   => g ott ffs
            Three => g ott sen
            Four  => g ffs ott
            Five  => g ffs ffs
            Six   => g ffs sen
            Seven => g sen ott
            Eight => g sen ffs
            Nine  => g sen sen

||| Validate that all of a Sudoku board's 3x3 squares are valid
sudokuSquaresValid : UnsafeSudoku -> Bool
sudokuSquaresValid s = all sudokuDigitsValid (map (sudokuSquare s) digits)
  where positions : List SudokuPosition
        positions = zip digits digits

||| Return true if an unvalidated Sudoku
||| board meets all validation requirements
sudokuValid : UnsafeSudoku -> Bool
sudokuValid u =
  case u of
    Empty      => True
    Move s p d =>
      sudokuVertsValid u && sudokuHorizontalsValid u && sudokuSquaresValid u &&
      case s of
        Empty         => True
        Move ss sp sd => (sudokuValid s) && not (sp == p)

||| Sudoku board whose validity is required
data Sudoku : Type where
  SafeSudoku : (s : UnsafeSudoku) -> { auto prf : sudokuValid s = True } -> Sudoku
