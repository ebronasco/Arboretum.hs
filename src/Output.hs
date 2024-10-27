{-# LANGUAGE PatternSynonyms #-}

{- |
Module      : Output
Description : Generate TeX output, pdf, and display it in a pdf viewer.
Copyright   : (c) University of Geneva, 2024
License     : MIT
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

Implementation of the @Texifiable@ typeclass, its instances for the
@Symbolics@ module and functions to display the output in a pdf viewer.
-}
module Output (
    Texifiable,
    texify,
    texifyParentheses,
    texifyDebug,
    texifyID,
    display,
    displayDebug,
) where

import Data.List (intercalate)
import GradedList (
    Graded,
    grading,
 )
import Symbolics (
    ScalarProduct,
    Sum (Zero),
    Vector (..),
    lengthV,
    toListS,
    toListV,
    pattern (:*^),
 )
import System.Directory (copyFile)
import System.Process.Typed
import Text.Printf

{- |
  To be displayed in a pdf using LaTeX, a type must be an
  instance of the @Texifiable@ typeclass.

  It is mandatory to define the @texify@ function. You can specify
  the parentheses of the type by defining @texifyParentheses@.
  You can also define @texifyDebug@ to display debug information
  and @texifyID@ to display the identifier of the type.
-}
class Texifiable a where
    -- | The main function of the typeclass. It returns the TeX code
    -- of @a@. Use @texifyP@ for recursion when defining this if you
    -- want the parentheses to be displayed.
    texify :: a -> String

    -- | Returns the TeX code of the left and right parentheses of
    -- @a@. By default, it returns the empty string for both.
    texifyParentheses :: a -> (String, String)
    texifyParentheses _ = ("", "")

    -- | The identifier of the type used for debugging. By default,
    -- it returns the empty string.
    texifyID :: a -> String
    texifyID _ = ""

    -- | Returns the TeX code of @a@ with debug information. Use
    -- @texifyD@ for recursion when defining this. By default, it
    -- returns the same as @texifyP@. The first two arguments are
    -- used to specify the levels of the syntax tree at which the
    -- debug information is displayed.
    texifyDebug :: Integer -> Integer -> a -> String
    texifyDebug _ _ = texifyP

    -- | Returns the TeX code of @a@ with parentheses. By default, it
    -- wraps @texify a@ with parentheses specified by
    -- @texifyParentheses@.
    texifyP :: a -> String
    texifyP x =
        fst (texifyParentheses x)
            ++ texify x
            ++ snd (texifyParentheses x)

    -- | Returns the TeX code of @a@ with debug information. By
    -- default, it wraps @texifyDebug a@ with underbrace and uses
    -- @texifyID@. The first two arguments are used to specify the
    -- levels of the syntax tree at which the debug information is
    -- displayed.
    texifyD :: Integer -> Integer -> a -> String
    texifyD i j x =
        underbrace i j (texifyID x) $
            texifyDebug (i - 1) (j - 1) x

{- | Wraps a string with an underbrace if @i <= 0 < j@ and non-empty
@name@.
-}
underbrace :: Integer -> Integer -> String -> String -> String
underbrace i j name str =
    if i <= 0 && j > 0 && not (null name)
        then
            "\\underbracket[0.1ex]{"
                ++ str
                ++ "}_{\\text{"
                ++ name
                ++ "}}"
        else str

-- | Instances for primitives.
instance Texifiable Char where
    texify c = [c]

instance Texifiable Integer where
    texify = show

instance Texifiable Int where
    texify = show

-- | Lists represent products.
instance
    ( Texifiable a
    , Eq a
    )
    => Texifiable [a]
    where
    texifyID _ = "Prod"
    texify os
        | null os = "1"
        | otherwise = intercalate " \\cdot " $ map texifyP os
    texifyDebug i j os
        | null os = "1"
        | otherwise = intercalate " \\cdot " $ map (texifyD i j) os
    texifyParentheses x =
        if length x > 1
            then ("(", ")")
            else ("", "")

-- | Tuples represent tensor products.
instance
    ( Texifiable a
    , Texifiable b
    )
    => Texifiable (a, b)
    where
    texifyID _ = "TenProd"
    texify (a, b) = texifyP a ++ " \\otimes " ++ texifyP b
    texifyDebug i j (a, b) =
        texifyD i j a
            ++ " \\otimes "
            ++ texifyD i j b
    texifyParentheses _ = ("(", ")")

-- | Instances for the types of the @Symbolics@ module.
instance
    ( Num k
    , Eq k
    , Texifiable k
    , Texifiable a
    )
    => Texifiable (ScalarProduct k a)
    where
    texifyID _ = "ScProd"
    texify (k :*^ v)
        | k == 1 = texifyP v
        | k == -1 = "-" ++ texifyP v
        | otherwise = texifyP k ++ texifyP v
    texifyDebug i j (k :*^ v) =
        texifyD i j k
            ++ " \\cdot "
            ++ texifyD i j v

instance
    ( Num k
    , Eq k
    , Eq a
    , Graded a
    , Texifiable k
    , Texifiable a
    )
    => Texifiable (Sum k a)
    where
    texifyID x = "Sum " ++ show (grading x)
    texify x = intercalate " + " $ map texify $ toListS x
    texifyDebug i j x =
        intercalate " + " $
            map (texifyD i j) $
                toListS x
    texifyParentheses x =
        if (length . toListS) x > 1
            then ("(", ")")
            else ("", "")

instance
    ( Num k
    , Eq k
    , Eq a
    , Graded a
    , Texifiable k
    , Texifiable a
    )
    => Texifiable (Vector k a)
    where
    texifyID _ = "PowSer"
    texify v =
        intercalate " + " $
            map texify $
                filter (/= Zero) $
                    toListV v
    texifyDebug i j v =
        intercalate " + " $
            map (texifyD i j) $
                filter (/= Zero) $
                    toListV v
    texifyParentheses x =
        if lengthV x > 1
            then ("(", ")")
            else ("", "")

{- |
  Generates a pdf file from a TeX string and displays it in a pdf.
  The function uses the template.tex file in the texput directory to
  generate a temporary TeX file. It then compiles it with pdflatex,
  pythontex, and pdflatex again. The resulting pdf is copied to the
  current directory and displayed in a pdf viewer.
-}
printPdf :: String -> IO ()
printPdf str = do
    templateStr <- readFile "texput/template.tex"
    let tex = printf templateStr str
    writeFile "texput/tmp.tex" tex

    runProcess_ $
        setStdout nullStream $
            setWorkingDir "texput" $
                proc "pdflatex" ["tmp.tex"]

    runProcess_ $
        setStdout nullStream $
            setWorkingDir "texput" $
                proc "pythontex" ["tmp.tex"]

    runProcess_ $
        setStdout nullStream $
            setWorkingDir "texput" $
                proc "pdflatex" ["tmp.tex"]

    copyFile "texput/tmp.pdf" "output.pdf"
    copyFile "texput/tmp.tex" "output.tex"

    runProcess_ $
        shell "zathura --synctex-forward :: output.pdf > /dev/null &"

    return ()

-- | Generate a TeX string from a type and display it in a pdf viewer.
display
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       , Texifiable k
       , Texifiable a
       )
    => Vector k a
    -> IO ()
display v = printPdf $ " $ " ++ texify v ++ " $ "

{- | Generate a TeX string with debug information from a type and
display it in a pdf viewer.
-}
displayDebug
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       , Texifiable k
       , Texifiable a
       )
    => Integer
    -> Integer
    -> Vector k a
    -> IO ()
displayDebug startLevel endLevel v =
    printPdf $
        " $ " ++ texifyDebug startLevel endLevel v ++ " $ "
