@echo off
del obj\*.fst.checked
SET OPTIONS=--cache_checked_modules --silent --cache_dir obj
echo AlgebraTypes
fstar AlgebraTypes.fst %OPTIONS%
echo Fraction Definition
fstar Fractions.Definition.fst %OPTIONS%
echo Fraction Equivalence
fstar Fractions.Equivalence.fst %OPTIONS%
echo Fraction Addition
fstar Fractions.Addition.fst %OPTIONS%
echo Fraction Multiplication
fstar Fractions.Multiplication.fst %OPTIONS%
echo Fraction Field
fstar Fractions.fst %OPTIONS%
echo FStar.IntegerIntervals
fstar FStar.IntegerIntervals.fst %OPTIONS%
echo FStar.Algebra.CommMonoid.Fold
fstar FStar.Algebra.CommMonoid.Fold.fst %OPTIONS%
echo FStar.Seq.Matrix
fstar FStar.Seq.Matrix.fst %OPTIONS%
echo FStar.Algebra.CommMonoid.Fold.Nested
fstar FStar.Algebra.CommMonoid.Fold.Nested.fst %OPTIONS%
echo Poly Definitions
fstar Polynomials.Definition.fst %OPTIONS%
echo Poly Equivalence
fstar Polynomials.Equivalence.fst %OPTIONS%
echo Poly Compact
fstar Polynomials.Compact.fst %OPTIONS%
echo Poly Addition
fstar Polynomials.Addition.fst %OPTIONS%
echo Poly Monomials
fstar Polynomials.Monomial.fst %OPTIONS%
echo Poly Multiplication
fstar Polynomials.Multiplication.fst %OPTIONS%
echo Poly Ring
fstar Polynomials.fst %OPTIONS%
echo RefinementEquality utility module
fstar RefinementEquality.fst %OPTIONS%
echo --- Recheck successful! ---
pause
