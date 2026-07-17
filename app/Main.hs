{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -w #-}

import Butcher.Aromatic
import Butcher.Graph
import Butcher.NonPlanar
import Butcher.Planar
import Butcher.Series
import Control.Monad.State.Lazy
import Core.Algebra
import Core.GradedList
import Core.Output
import Core.SyntacticTree
import Core.VectorSpace
import Data.List
import Data.MultiSet as MS
import Data.Ratio

{-|
  This file contains the implementation of:
   1. connection algebra and Gavrilov's alpha and lambda maps,
   2. connection tensor algebra and Gavrilov's K and beta maps as well as their inverses,
   3. Gavrilov's double-exponential map q,
   4. Lie algebra and the function `oneside` that rewrites a term with arbitrary bracketing as a linera combination of terms [x, ...] where x is a generator,
   5. Special polynomials and the map $special$ that sends a Lie monomial to a special polynomial.

   All these maps are taken from 
    Al-Kaabi, M. J. H., Ebrahimi-Fard, K., Manchon, D., & Munthe-Kaas, H. Z. (2023). Algebraic aspects of connections: From torsion, curvature, and post-Lie algebras to Gavrilov’s double exponential and special polynomials. Journal of Noncommutative Geometry, 19(1), 297–335. https://doi.org/10.4171/jncg/539
-}


---------------------------------------------------------------------

-- * Connection (tensor) algebra and Gavrilov's alpha, lambda, K, beta and q maps

---------------------------------------------------------------------

-- | Connection monomial
data ConnMono a = Conn (ConnMono a) (ConnMono a) | ConnGen a deriving (Eq, Ord)

-- | Define a way to write a connection monomial as a string to print in the terminal
instance (Show a) => Show (ConnMono a) where
    show (ConnGen c) = show c
    show (Conn t1 t2) = "(" ++ show t1 ++ " |> " ++ show t2 ++ ")"

-- | Define a way to write a connection monomial as TeX to print to a PDF file
instance (Texifiable a) => Texifiable (ConnMono a) where
    texify (ConnGen c) = texify c
    texify (Conn a b) = "(" ++ texify a ++ " \\triangleright " ++ texify b ++ ")"

-- | Define grading of connection monomials which is required to use them as a basis
instance (Graded a) => Graded (ConnMono a) where
    grading (ConnGen c) = grading c
    grading (Conn t1 t2) = grading t1 + grading t2

-- | Define the vector space spanned by connection monomials over the field of rationals
instance (Eq a, Graded a) => IsVector (ConnMono a) where
    type VectorScalar (ConnMono a) = Rational
    type VectorBasis (ConnMono a) = ConnMono a
    vector = vector . (1 *^)

-- | (Non-unital) connection algebra is the vector space spanned by connection monomials
type ConnAlgebra a = Vector Rational (ConnMono a)

-- | The derivation used in the definition of the alpha and lambda maps
delta :: (Eq a, Graded a) => ConnMono a -> ConnMono a -> ConnAlgebra a
delta a b@(ConnGen c) = vector $ Conn a b
delta a (Conn b c) =
    linear (\y -> Conn y c) (delta a b)
        <> linear (Conn b) (delta a c)

-- | Gavrilov's alpha map following the definition (2.29) from the paper
alpha :: (Eq a, Graded a) => ConnMono a -> ConnAlgebra a
alpha y = expOp (scale (-1) . delta y) $ vector y

-- | Gavrilov's lambda map following the definition (2.29) from the paper
lambda :: (Eq a, Graded a) => ConnMono a -> ConnMono a -> ConnAlgebra a
lambda y z = expOp (scale (-1) . delta y) $ vector z

-- | Connection tensor algebra is the vector space spanned by lists of connection monomials. The product is given by concatenation of lists and the unit is the empty list.
type ConnTenAlgebra a = Vector Rational [ConnMono a]

-- | Extend the connection product `ConnMono a -> ConnMono a -> ConnMono a` to `ConnMono a -> [ConnMono a] -> ConnTenAlgebra a` as a derivation in the second argument.
der :: (Eq a, Graded a) => ConnMono a -> [ConnMono a] -> ConnTenAlgebra a
der x [] = Empty
der x (y : ys) = vector (Conn x y : ys) + vector [y] * der x ys

-- | Gavrilov's K map as defined in (2.22) in the paper
gavK :: (Eq a, Graded a) => [ConnMono a] -> ConnTenAlgebra a
gavK [] = vector []
gavK (x : xs) = vector [x] * gavK xs - linear gavK (der x xs)

-- | Inverse of the Gavrilov's K map using the fact that its a morphism from concatenation to Grossman-Larson
gavKinv :: (Eq a, Graded a) => [ConnMono a] -> ConnTenAlgebra a
gavKinv [] = vector []
gavKinv (x : xs) =
    vector [x] * vector (gavKinv xs)
        + linear (der x) (gavKinv xs)

-- | Gavrilov's beta map as defined in Lemma 3 in the paper, see also the definition of map Z in section 2.5.3
beta :: (Eq a, Graded a) => ConnTenAlgebra a -> ConnTenAlgebra a
beta = logV . linearGraded gavK . expV

-- | Inverse of the Gavrilov's beta map using the inverse of the Gavrilov's K map
betaInv :: (Eq a, Graded a) => ConnTenAlgebra a -> ConnTenAlgebra a
betaInv = logV . linearGraded gavKinv . expV

-- | Gavrilov's double-exponential map using a simplified form of (6.1)
q :: (Eq a, Graded a) => ConnMono a -> ConnMono a -> ConnTenAlgebra a
q v w =
    logV $
        linearGraded gavKinv $
            (linearGraded gavK $ expV $ vector [v])
                * (linearGraded gavK $ expV $ linearGraded (: []) $ lambda v w)

q' :: (Eq a, Graded a) => ConnMono a -> ConnMono a -> ConnTenAlgebra a
q' v w = linearGraded removeDer $ beta $ logV $ expV (vector [v]) * expV (vector [w])
  where
    removeDer a = if (any hasDer a) then Empty else vector a
    hasDer (Conn _ _) = True
    hasDer _ = False

q'' :: (Eq a, Graded a) => ConnMono a -> ConnMono a -> ConnTenAlgebra a
q'' v w = logV $ linearGraded gavKinv $ expV $ linearGraded gavKinv $ logV $ linearGraded gavK $ expV (vector [v]) * expV (vector [w])


---------------------------------------------------------------------

-- * Lie algebra

---------------------------------------------------------------------

-- | A Lie monomial with arbitrary bracketing
data LieMono a = Br (LieMono a) (LieMono a) | LieGen a deriving (Eq)

-- | Define a way to write a Lie monomial as a string to print in the terminal
instance (Show a) => Show (LieMono a) where
    show (LieGen c) = show c
    show (Br b1 b2) = "[" ++ show b1 ++ ", " ++ show b2 ++ "]"

-- | Define a way to write a Lie monomial as TeX to print to a PDF file
instance (Texifiable a) => Texifiable (LieMono a) where
    texify (LieGen c) = texify c
    texify (Br a b) = "[" ++ texify a ++ ", " ++ texify b ++ "]"

-- | Define grading of Lie monomials which is required to use them as a basis
instance (Graded a) => Graded (LieMono a) where
    grading (LieGen c) = grading c
    grading (Br b1 b2) = grading b1 + grading b2

-- | Define the vector space spanned by Lie monomials over the field of rationals
instance (Eq a, Graded a) => IsVector (LieMono a) where
    type VectorScalar (LieMono a) = Rational
    type VectorBasis (LieMono a) = LieMono a
    vector = vector . (1 *^)

-- | A Lie algebra is the vector space spanned by Lie monomials
type LieAlgebra a = Vector Rational (LieMono a)

-- | Transform a Lie monomial with arbitrary bracketing into a linear combination of terms of the form [x, ...] where x is a generator. This follows the argument from the proof of Theorem 5.
oneside :: (Eq a, Graded a) => LieMono a -> LieAlgebra a
oneside (LieGen c) = vector $ LieGen c
oneside a@(Br (LieGen _) _) = vector a
oneside (Br (Br b c) d) =
    (vector $ oneside $ Br b (Br c d))
        <> (scale (-1) $ vector $ oneside $ Br c (Br b d))


---------------------------------------------------------------------

-- * Special polynomials

---------------------------------------------------------------------

-- | Special monomials are nested expressions consisting of the derivatives of S and Tor, as well as the application of S(a, b) onto a special monomial.
data SpecMono a
    = S [SpecMono a] (SpecMono a) (SpecMono a)
    | Tor [SpecMono a] (SpecMono a) (SpecMono a)
    | CD (SpecMono a) (SpecMono a)
    | SpecGen a
    deriving (Eq)

-- | Define a way to write a special monomial as a string to print in the terminal
instance (Show a) => Show (SpecMono a) where
    show (S [] a b) = "S(" ++ show a ++ ", " ++ show b ++ ")"
    show (S ds a b) = "dS" ++ show ds ++ "(" ++ show a ++ ", " ++ show b ++ ")"
    show (Tor [] a b) = "T(" ++ show a ++ ", " ++ show b ++ ")"
    show (Tor ds a b) = "dT" ++ show ds ++ "(" ++ show a ++ ", " ++ show b ++ ")"
    show (CD a b) = "(" ++ show a ++ " |> " ++ show b ++ ")"
    show (SpecGen c) = show c

-- | Define a way to write a special monomial as TeX to print to a PDF file
instance (Eq a, Texifiable a) => Texifiable (SpecMono a) where
    texify (S [] a b) = "S(" ++ texify a ++ ", " ++ texify b ++ ")"
    texify (S ds a b) = "dS[" ++ texify ds ++ "](" ++ texify a ++ ", " ++ texify b ++ ")"
    texify (Tor [] a b) = "T(" ++ texify a ++ ", " ++ texify b ++ ")"
    texify (Tor ds a b) = "dT[" ++ texify ds ++ "](" ++ texify a ++ ", " ++ texify b ++ ")"
    texify (CD a b) = "(" ++ texify a ++ " \\triangleright " ++ texify b ++ ")"
    texify (SpecGen c) = texify c

-- | Define grading of special monomials which is required to use them as a basis
instance (Graded a) => Graded (SpecMono a) where
    grading (S ds a b) = grading ds + grading a + grading b
    grading (Tor ds a b) = grading ds + grading a + grading b
    grading (CD a b) = grading a + grading b
    grading (SpecGen c) = grading c

-- | Define the vector space spanned by special monomials over the field of rationals
instance (Eq a, Graded a) => IsVector (SpecMono a) where
    type VectorScalar (SpecMono a) = Rational
    type VectorBasis (SpecMono a) = SpecMono a
    vector = vector . ((1 % 1) *^)

-- | The vector space of special polynomials is spanned by special monomials
type SpecialPolys a = Vector Rational (SpecMono a)

-- | Rewrite an element of the Lie algebra written in terms of bracket as a special polynomial.
special :: (Eq a, Graded a, Show a) => LieMono a -> SpecialPolys a
special = linear perTerm . oneside
  where
    perTerm e = rhoKer e <> rhoIm e


type SpecTenAlgebra a = Vector Rational [SpecMono a]

derTen :: (Eq a, Graded a) => SpecMono a -> [SpecMono a] -> SpecTenAlgebra a
derTen x [] = Empty
derTen x (y : ys) = (linear (\z -> z:ys) $ derTerm x y) + vector [y] * derTen x ys
  where
    derTerm a (SpecGen c) = vector $ CD a (SpecGen c)
    derTerm a (CD b c) = vector $ CD a (CD b c)
    derTerm a (S ds b c) =
        vector (S (a : ds) b c)
            <> linear (\y -> S ds y c) (derTerm a b)
            <> linear (S ds b) (derTerm a c)
    derTerm a (Tor ds b c) =
        vector (Tor (a : ds) b c)
            <> linear (\y -> Tor ds y c) (derTerm a b)
            <> linear (Tor ds b) (derTerm a c)

-- | Gavrilov's K map as defined in (2.22) in the paper
gavKS :: (Eq a, Graded a) => [SpecMono a] -> SpecTenAlgebra a
gavKS [] = vector []
gavKS (x : xs) = vector [x] * gavKS xs - linear gavKS (derTen x xs)


-- | Gavrilov's beta map as defined in Lemma 3 in the paper, see also the definition of map Z in section 2.5.3
betaS :: (Eq a, Graded a) => SpecTenAlgebra a -> SpecTenAlgebra a
betaS = logV . linearGraded gavKS . expV







-- | Compute the kernel part of the expression following Hans' working notes.
rhoKer :: (Eq a, Graded a, Show a) => LieMono a -> SpecialPolys a
rhoKer (LieGen _) = Empty
rhoKer (Br (LieGen x) (LieGen y)) = vector $ S [] (SpecGen x) (SpecGen y)
rhoKer (Br (LieGen x) a) =
    linear (S [] (SpecGen x)) (linear rhoIm $ oneside a)
        <> linear (derOp (SpecGen x)) (linear rhoKer $ oneside a)
rhoKer a = error $ "rhoKer got an unexpected term: " ++ show a

-- | Compute the image part of the expression following Hans' working notes.
rhoIm :: (Eq a, Graded a, Show a) => LieMono a -> SpecialPolys a
rhoIm (LieGen x) = vector $ SpecGen x
rhoIm (Br (LieGen x) (LieGen y)) = scale (-1) $ vector $ Tor [] (SpecGen x) (SpecGen y)
rhoIm (Br (LieGen x) a) =
    linear (\y -> CD y (SpecGen x)) (linear rhoKer $ oneside a)
        <> scale (-1) (linear (Tor [] (SpecGen x)) (linear rhoIm $ oneside a))
        <> linear (derOp (SpecGen x)) (linear rhoIm $ oneside a)
rhoIm a = error $ "rhoIm got an unexpected term: " ++ show a

-- | Derivation of the torsion and curvature tensors. Note that the derivation of a tensor does not touch the arguments due to its Leibniz definition.
derOp :: (Eq a, Graded a) => SpecMono a -> SpecMono a -> SpecialPolys a
derOp a (SpecGen c) = Empty
derOp a (CD b c) = Empty
derOp a (S ds b c) =
    vector (S (a : ds) b c)
        <> linear (\y -> S ds y c) (derOp a b)
        <> linear (S ds b) (derOp a c)
derOp a (Tor ds b c) =
    vector (Tor (a : ds) b c)
        <> linear (\y -> Tor ds y c) (derOp a b)
        <> linear (Tor ds b) (derOp a c)






main :: IO ()
main = do
    putStrLn ""
    putStrLn "================================="
    putStrLn ""
    putStrLn "Let us repeat the computations performed in the paper."
    putStrLn ""
    putStrLn "The formula for alpha of y given in (2.27) can be computed by the following command (without >>>):"
    putStrLn ""
    putStrLn ">>> display $ takeGrading 5 $ alpha $ ConnGen 'y'"
    putStrLn ""
    putStrLn "where"
    putStrLn "\t`ConnGen 'y'` creates an element of the connection algebra out of a character 'y',"
    putStrLn "\t`alpha` computes the expression,"
    putStrLn "\t`takeGrading 5` takes the first 5 gradings (including 0),"
    putStrLn "\t`display` generates the PDF displaying the resulting formula."
    putStrLn ""
    putStrLn "Similarly, we can compute the expression for lambda of y and z:"
    putStrLn ""
    putStrLn ">>> display $ takeGrading 5 $ lambda (ConnGen 'y') (ConnGen 'z')"
    putStrLn ""
    putStrLn "The example for the Gavrilov's K map in Section 2.5.1 can be computed as"
    putStrLn ""
    putStrLn ">>> display $ gavK $ [ConnGen 'x', ConnGen 'y', ConnGen 'z']"
    putStrLn ""
    putStrLn "where the list denotes concatenation."
    putStrLn ""
    putStrLn "The example for the inverse of the Gavrilov's K map can be computed as"
    putStrLn ""
    putStrLn ">>> display $ gavKinv $ [ConnGen 'x', ConnGen 'y', ConnGen 'z']"
    putStrLn ""
    putStrLn "The formula for Z from the end of Section 2.5.3 and the formula for beta in Section 3 can be computed as"
    putStrLn ""
    putStrLn ">>> display $ takeGrading 4 $ beta $ vector [ConnGen 'y']"
    putStrLn ""
    putStrLn "Out of curiousity, let us also compute the inverse of beta,"
    putStrLn ""
    putStrLn ">>> display $ takeGrading 4 $ betaInv $ vector [ConnGen 'y']"
    putStrLn ""
    putStrLn "The formula for the Gavrilov's double-exponential map q can be computed as"
    putStrLn ""
    putStrLn ">>> display $ takeGrading 5 $ q (ConnGen 'v') (ConnGen 'w')"
    putStrLn ""
    putStrLn "Note that the last computation returns an element of the tensor algebra. From the definition of q, we know that this element is inside the Lie algebra of primitive elements. Its automatical rewritting in terms of Lie brackets is in active development and will be available in the next version of the code. For now, we can rewrite it manually as,"
    putStrLn ""
    putStrLn ">>> a = vector (LieGen 'v') <> vector (LieGen 'w') <> (scale (1 % 2) $ vector $ Br (LieGen 'v') (LieGen 'w')) <> (scale (1 % 12) $ vector $ Br (LieGen 'v') (Br (LieGen 'v') (LieGen 'w'))) <> (scale (1 % 12) $ vector $ Br (Br (LieGen 'v') (LieGen 'w')) (LieGen 'w')) <> (scale (1 % 24) $ vector $ Br (LieGen 'v') (Br (Br (LieGen 'v') (LieGen 'w')) (LieGen 'w')))"
    putStrLn ""
    putStrLn "and display it as"
    putStrLn ""
    putStrLn ">>> display a"
    putStrLn ""
    putStrLn "We would like to write this expression as a special polynomial. For that, we first reduce all brackets to the form [x, ...] where x is a generator. We do so by using the `oneside` function as follows,"
    putStrLn ""
    putStrLn ">>> b = Br (Br (LieGen 'a') (LieGen 'b')) (Br (LieGen 'c') (LieGen 'd'))"
    putStrLn ">>> display $ oneside b"
    putStrLn ""
    putStrLn "This reproduces the example from the proof of Theorem 5. Note that we apply the Jacobi identity in a different manner than is done in the example from the proof of Theorem 5, therefore, our expressions differ."
    putStrLn ""
    putStrLn "Finally, we can write the Lie polynomial `a` computed before as a special polynomial using the function `special`,"
    putStrLn ""
    putStrLn ">>> display $ linear special a"
    putStrLn ""
    putStrLn ""
    putStrLn ""
    putStrLn ""
    putStrLn "Type \":quit\" to exit."
