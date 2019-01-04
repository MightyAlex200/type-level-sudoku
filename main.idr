module Main

%default total

data SudokuDigit : Type where
  SudokuValid : (n : Nat) -> { auto gte : n `GTE` 1 } -> { auto lte : n `LTE` 9 } -> SudokuDigit

implementation Eq SudokuDigit where
  (SudokuValid (n1)) == (SudokuValid (n2)) = n1 == n2

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
digits = [ SudokuValid 1
         , SudokuValid 2
         , SudokuValid 3
         , SudokuValid 4
         , SudokuValid 5
         , SudokuValid 6
         , SudokuValid 7
         , SudokuValid 8
         , SudokuValid 9
         ]

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
positionSquare (SudokuValid x, SudokuValid y) =
  case (toIntegerNat x) of
    1 => c1
    2 => c1
    3 => c1
    4 => c2
    5 => c2
    6 => c2
    7 => c3
    8 => c3
    9 => c3
    _ => assert_unreachable
  where
    c1 : SudokuDigit
    c1 =
      case toIntegerNat y of
        1 => SudokuValid 1
        2 => SudokuValid 1
        3 => SudokuValid 1
        4 => SudokuValid 4
        5 => SudokuValid 4
        6 => SudokuValid 4
        7 => SudokuValid 7
        8 => SudokuValid 7
        9 => SudokuValid 7
        _ => assert_unreachable
    c2 : SudokuDigit
    c2 =
      case toIntegerNat y of
        1 => SudokuValid 2
        2 => SudokuValid 2
        3 => SudokuValid 2
        4 => SudokuValid 5
        5 => SudokuValid 5
        6 => SudokuValid 5
        7 => SudokuValid 8
        8 => SudokuValid 8
        9 => SudokuValid 8
        _ => assert_unreachable
    c3 : SudokuDigit
    c3 =
      case toIntegerNat y of
        1 => SudokuValid 3
        2 => SudokuValid 3
        3 => SudokuValid 3
        4 => SudokuValid 6
        5 => SudokuValid 6
        6 => SudokuValid 6
        7 => SudokuValid 9
        8 => SudokuValid 9
        9 => SudokuValid 9
        _ => assert_unreachable

sudokuSquare : UnsafeSudoku -> SudokuPosition -> List SudokuDigit
sudokuSquare s p = mapMaybe (sudokuPosition s) positions
  where squareDigit : SudokuDigit
        squareDigit = positionSquare p
        positions =
          case squareDigit of
            SudokuValid n => 
              case toIntegerNat n of
                1 => [ (SudokuValid 1, SudokuValid 1)
                    , (SudokuValid 2, SudokuValid 1)
                    , (SudokuValid 3, SudokuValid 1)
                    , (SudokuValid 1, SudokuValid 2)
                    , (SudokuValid 2, SudokuValid 2)
                    , (SudokuValid 3, SudokuValid 2)
                    , (SudokuValid 1, SudokuValid 3)
                    , (SudokuValid 2, SudokuValid 3)
                    , (SudokuValid 3, SudokuValid 3)
                    ]
                2 => [ (SudokuValid 4, SudokuValid 1)
                    , (SudokuValid 5, SudokuValid 1)
                    , (SudokuValid 6, SudokuValid 1)
                    , (SudokuValid 4, SudokuValid 2)
                    , (SudokuValid 5, SudokuValid 2)
                    , (SudokuValid 6, SudokuValid 2)
                    , (SudokuValid 4, SudokuValid 3)
                    , (SudokuValid 5, SudokuValid 3)
                    , (SudokuValid 6, SudokuValid 3)
                    ]
                3 => [ (SudokuValid 7, SudokuValid 1)
                    , (SudokuValid 8, SudokuValid 1)
                    , (SudokuValid 9, SudokuValid 1)
                    , (SudokuValid 7, SudokuValid 2)
                    , (SudokuValid 8, SudokuValid 2)
                    , (SudokuValid 9, SudokuValid 2)
                    , (SudokuValid 7, SudokuValid 3)
                    , (SudokuValid 8, SudokuValid 3)
                    , (SudokuValid 9, SudokuValid 3)
                    ]
                4 => [ (SudokuValid 1, SudokuValid 4)
                    , (SudokuValid 2, SudokuValid 4)
                    , (SudokuValid 3, SudokuValid 4)
                    , (SudokuValid 1, SudokuValid 5)
                    , (SudokuValid 2, SudokuValid 5)
                    , (SudokuValid 3, SudokuValid 5)
                    , (SudokuValid 1, SudokuValid 6)
                    , (SudokuValid 2, SudokuValid 6)
                    , (SudokuValid 3, SudokuValid 6)
                    ]
                5 => [ (SudokuValid 4, SudokuValid 4)
                    , (SudokuValid 5, SudokuValid 4)
                    , (SudokuValid 6, SudokuValid 4)
                    , (SudokuValid 4, SudokuValid 5)
                    , (SudokuValid 5, SudokuValid 5)
                    , (SudokuValid 6, SudokuValid 5)
                    , (SudokuValid 4, SudokuValid 6)
                    , (SudokuValid 5, SudokuValid 6)
                    , (SudokuValid 6, SudokuValid 6)
                    ]
                6 => [ (SudokuValid 7, SudokuValid 4)
                    , (SudokuValid 8, SudokuValid 4)
                    , (SudokuValid 9, SudokuValid 4)
                    , (SudokuValid 7, SudokuValid 5)
                    , (SudokuValid 8, SudokuValid 5)
                    , (SudokuValid 9, SudokuValid 5)
                    , (SudokuValid 7, SudokuValid 6)
                    , (SudokuValid 8, SudokuValid 6)
                    , (SudokuValid 9, SudokuValid 6)
                    ]
                7 => [ (SudokuValid 1, SudokuValid 7)
                    , (SudokuValid 2, SudokuValid 7)
                    , (SudokuValid 3, SudokuValid 7)
                    , (SudokuValid 1, SudokuValid 8)
                    , (SudokuValid 2, SudokuValid 8)
                    , (SudokuValid 3, SudokuValid 8)
                    , (SudokuValid 1, SudokuValid 9)
                    , (SudokuValid 2, SudokuValid 9)
                    , (SudokuValid 3, SudokuValid 9)
                    ]
                8 => [ (SudokuValid 4, SudokuValid 7)
                    , (SudokuValid 5, SudokuValid 7)
                    , (SudokuValid 6, SudokuValid 7)
                    , (SudokuValid 4, SudokuValid 8)
                    , (SudokuValid 5, SudokuValid 8)
                    , (SudokuValid 6, SudokuValid 8)
                    , (SudokuValid 4, SudokuValid 9)
                    , (SudokuValid 5, SudokuValid 9)
                    , (SudokuValid 6, SudokuValid 9)
                    ]
                9 => [ (SudokuValid 7, SudokuValid 7)
                    , (SudokuValid 8, SudokuValid 7)
                    , (SudokuValid 9, SudokuValid 7)
                    , (SudokuValid 7, SudokuValid 8)
                    , (SudokuValid 8, SudokuValid 8)
                    , (SudokuValid 9, SudokuValid 8)
                    , (SudokuValid 7, SudokuValid 9)
                    , (SudokuValid 8, SudokuValid 9)
                    , (SudokuValid 9, SudokuValid 9)
                    ]
                _ => assert_unreachable

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
