module Main
import Sudoku

%default total

sudokuDigitToIndex : SudokuDigit -> Nat
sudokuDigitToIndex One   = 0
sudokuDigitToIndex Two   = 1
sudokuDigitToIndex Three = 2
sudokuDigitToIndex Four  = 3
sudokuDigitToIndex Five  = 4
sudokuDigitToIndex Six   = 5
sudokuDigitToIndex Seven = 6
sudokuDigitToIndex Eight = 7
sudokuDigitToIndex Nine  = 8

integerToDigit : Integer -> Maybe SudokuDigit
integerToDigit 1 = Just One
integerToDigit 2 = Just Two
integerToDigit 3 = Just Three
integerToDigit 4 = Just Four
integerToDigit 5 = Just Five
integerToDigit 6 = Just Six
integerToDigit 7 = Just Seven
integerToDigit 8 = Just Eight
integerToDigit 9 = Just Nine
integerToDigit _ = Nothing

replaceInList : List a -> Nat -> (a -> a) -> List a
replaceInList [] Z f = []
replaceInList (x :: xs) Z f = f x :: xs
replaceInList [] (S k) f = []
replaceInList (x :: xs) (S k) f = x :: replaceInList xs k f

sudokuToMatrix : UnsafeSudoku -> List (List (Maybe SudokuDigit))
sudokuToMatrix Empty = replicate 9 (replicate 9 Nothing)
sudokuToMatrix (Move s (x, y) d) =
  replaceInList (sudokuToMatrix s) (sudokuDigitToIndex y)
    (\row =>
      replaceInList row (sudokuDigitToIndex x) (const (Just d))
    )

showMatrix : List (List (Maybe SudokuDigit)) -> String
showMatrix m =
  unlines
    (intersperse
      "|-------|-------|-------|"
      (map 
        (\row =>
          unwords
            ("|" :: (pipeThrees
              (map
                (\md =>
                  case md of Just d  => show (1 + (sudokuDigitToIndex d))
                             Nothing => " ")
                row))))
        m))
  where pipeThrees : List String -> List String
        pipeThrees [] = []
        pipeThrees (x :: xs) =
          -- This is total because the only missing case for modNat is Z
          if (assert_total ((length xs) `modNat` 3)) == 0
          then x :: "|" :: pipeThrees xs
          else x :: pipeThrees xs

implementation Show UnsafeSudoku where
  show s = showMatrix (sudokuToMatrix s)

implementation Show Sudoku where
  show (SafeSudoku s) = show s

partial
askDigit : String -> IO SudokuDigit
askDigit s = do putStr ("Please enter the " ++ s ++ " of your next move: ")
                input <- getLine
                case integerToDigit (cast input) of
                  Just d => pure d
                  Nothing => do putStrLn ("Invalid input `" ++ input ++ "`")
                                askDigit s

partial
askCoordinate : String -> IO SudokuDigit
askCoordinate c = askDigit (c ++ " coordinate")

reqTrue : (b : Bool) -> (b = True -> a) -> Maybe a
reqTrue b f =
  case b of
    True => Just (f Refl)
    False => Nothing

partial
runSudoku : Sudoku -> IO ()
runSudoku s = do putStrLn "This is the current state of the board:"
                 putStrLn (show s)
                 x <- askCoordinate "x"
                 y <- askCoordinate "y"
                 d <- askDigit "digit"
                 case s of
                   SafeSudoku u =>
                     let nu = Move u (x, y) d
                         isValid = sudokuValid nu
                     in case reqTrue isValid (\p => SafeSudoku nu {prf = p}) of
                          Just ns => runSudoku ns
                          Nothing => do putStrLn "Invalid inputs. Please try again."
                                        runSudoku s

partial
main : IO ()
main = runSudoku (SafeSudoku Empty)
