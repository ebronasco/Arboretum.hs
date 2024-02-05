module Output (
    Texifiable,
    texify,
    texifyD,
    texifyID,
    display,
    displayDebug,
) where

import Data.List (intercalate)
import System.Process.Typed
import System.Directory(copyFile)
import Text.Printf

import Symbolics

class Texifiable a where
    texify :: a -> String          -- use texify or texifyP for recursion when defining this
    
    texifyParentheses :: a -> (String, String)
    texifyParentheses _ = ("", "")

    texifyID :: a -> String
    texifyID _ = ""

    texifyDebug :: Integer -> Integer -> a -> String -- use texifyD i j for recursion when defining this
    texifyDebug _ _ = texifyP

    -- returns tex code with parentheses
    texifyP :: a -> String
    texifyP x = (fst $ texifyParentheses x) ++ (texify x) ++ (snd $ texifyParentheses x)

    -- returns tex code of the math expression with debug information
    texifyD :: Integer -> Integer -> a -> String
    texifyD i j x = underbrace i j (texifyID x) $ (fst $ texifyParentheses x) ++ (texifyDebug (i-1) (j-1) x) ++ (snd $ texifyParentheses x)

underbrace :: Integer -> Integer -> String -> String -> String
underbrace i j name str = if (i <= 0 && j > 0 && (length name > 0)) 
                          then ("\\underbracket[0.1ex]{" ++ str ++ "}_{\\text{" ++ name ++ "}}") 
                          else str

instance Texifiable Char where
    texify c = [c]

instance Texifiable Integer where
    texify = show

instance (Texifiable k, Texifiable a) => Texifiable (Term k a) where
    texifyID _                 = "ScProd"
    texify (Term k v)          = (texifyP k) ++ " " ++ (texifyP v)
    texifyDebug i j (Term k v) = (texifyD i j k) ++ " \\cdot " ++ (texifyD i j v)

instance (Texifiable k, Scalar k, Basis a, Texifiable a) => Texifiable (PowerSeries k a) where
    texifyID _                = "PowSer"
    texify v                  = intercalate " + " $ map texify $ terms v
    texifyDebug i j v         = intercalate " + " $ map (texifyD i j) $ terms v
    texifyParentheses x       = if (lengthV x == 0 || lengthV x == 1) then ("(",")") else ("","")

instance (Texifiable a) => Texifiable [a] where
    texifyID _                 = "Prod"
    texify os          = intercalate " \\cdot " $ map texifyP os
    texifyDebug i j os = intercalate " \\cdot " $ map (texifyD i j) os
    texifyParentheses x     = if length x > 1 then ("(",")") else ("","")

 -- Take a string and apply pdflatex, pythontex, pdflatex to it to obtain a pdf
printPdf :: String -> IO ()
printPdf str = do
    templateStr <- readFile "texput/template.tex"
    let tex = printf templateStr str
    writeFile "texput/tmp.tex" tex
    runProcess_ $ setStdout nullStream $ setWorkingDir "texput" $ proc "pdflatex" ["tmp.tex"]
    runProcess_ $ setStdout nullStream $ setWorkingDir "texput" $ proc "pythontex" ["tmp.tex"]
    runProcess_ $ setStdout nullStream $ setWorkingDir "texput" $ proc "pdflatex" ["tmp.tex"]
    copyFile "texput/tmp.pdf" "output.pdf"
    runProcess_ $ shell "zathura --synctex-forward :: output.pdf > /dev/null &"
    return ()

display :: (Texifiable k, Texifiable a, Scalar k, Basis a) => PowerSeries k a -> IO ()
display v = printPdf $ " $ " ++ (texify v) ++ " $ "

displayDebug :: (Texifiable k, Texifiable a, Scalar k, Basis a) => Integer -> Integer -> PowerSeries k a -> IO ()
displayDebug startLevel endLevel v = printPdf $ " $ " ++ (texifyDebug startLevel endLevel v) ++ " $ "
