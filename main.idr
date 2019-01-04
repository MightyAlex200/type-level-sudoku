module Main

%default total

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

div3case : SudokuDigit -> a -> a -> a -> a
div3case One c1 c2 c3 = c1
div3case Two c1 c2 c3 = c1
div3case Three c1 c2 c3 = c1
div3case Four c1 c2 c3 = c2
div3case Five c1 c2 c3 = c2
div3case Six c1 c2 c3 = c2
div3case Seven c1 c2 c3 = c3
div3case Eight c1 c2 c3 = c3
div3case Nine c1 c2 c3 = c3

SudokuPosition : Type
SudokuPosition = (SudokuDigit, SudokuDigit)

data UnsafeSudoku : Type where
  Empty : UnsafeSudoku
  Move  : (s : UnsafeSudoku) -> (p : SudokuPosition) -> (d : SudokuDigit) -> UnsafeSudoku

sudokuPosition : UnsafeSudoku -> SudokuPosition -> Maybe SudokuDigit
sudokuPosition Empty p = Nothing
sudokuPosition (Move s ps d) p =
  if p == ps
  then Just d
  else sudokuPosition s p

sudokuDigitsValid : List SudokuDigit -> Bool
sudokuDigitsValid [] = True
sudokuDigitsValid (x :: xs) = (not (x `elem` xs)) && (sudokuDigitsValid xs)

digits : List SudokuDigit
digits = [ One,   Two,   Three
         , Four,  Five,  Six
         , Seven, Eight, Nine ]

sudokuVert : UnsafeSudoku -> SudokuDigit -> List SudokuDigit
sudokuVert s d = mapMaybe (sudokuPosition s) positions
  where positions : List SudokuPosition
        positions = map (MkPair d) digits

sudokuVertsValid : UnsafeSudoku -> Bool
sudokuVertsValid s = all sudokuDigitsValid (map (sudokuVert s) digits)

sudokuHorizontal : UnsafeSudoku -> SudokuDigit -> List SudokuDigit
sudokuHorizontal s d = mapMaybe (sudokuPosition s) positions
  where positions : List SudokuPosition
        positions = map (flip MkPair d) digits

sudokuHorizontalsValid : UnsafeSudoku -> Bool
sudokuHorizontalsValid s = all sudokuDigitsValid (map (sudokuHorizontal s) digits)

-- Each SudokuPosition maps to a 3x3 square representable by digits
-- 1 2 3
-- 4 5 6
-- 7 8 9
positionSquare : SudokuPosition -> SudokuDigit
positionSquare (x, y) =
  div3case x
    (div3case y One Four Seven)
    (div3case y Two Five Eight)
    (div3case y Three Six Nine)

sudokuSquare : UnsafeSudoku -> SudokuPosition -> List SudokuDigit
sudokuSquare s p = mapMaybe (sudokuPosition s) positions
  where squareDigit : SudokuDigit
        squareDigit = positionSquare p
        ott : List SudokuDigit
        ott = [One, Two, Three]
        ffs : List SudokuDigit
        ffs = [Four, Five, Six]
        sen : List SudokuDigit
        sen = [Seven, Eight, Nine]
        g : List SudokuDigit -> List SudokuDigit -> List SudokuPosition
        g a b =
          concatMap (\ea => map (MkPair ea) b) a
        positions =
          case squareDigit of
            One   => g ott ott
            Two   => g ott ffs
            Three => g ott sen
            Four  => g ffs ott
            Five  => g ffs ffs
            Six   => g ffs sen
            Seven => g sen ott
            Eight => g sen ffs
            Nine  => g sen sen

sudokuSquaresValid : UnsafeSudoku -> Bool
sudokuSquaresValid s = all sudokuDigitsValid (map (sudokuSquare s) positions)
  where positions : List SudokuPosition
        positions = zip digits digits

sudokuValid : UnsafeSudoku -> Bool
sudokuValid u =
  case u of
    Empty      => True
    Move s p d =>
      sudokuVertsValid u && sudokuHorizontalsValid u && sudokuSquaresValid u &&
      case s of
        Empty         => True
        Move ss sp sd => (sudokuValid s) && not (sp == p)

data Sudoku : Type where
  SafeSudoku : (s : UnsafeSudoku) -> { auto prf : sudokuValid s = True } -> Sudoku
