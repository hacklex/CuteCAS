del *.fst.checked
echo off
echo AlgebraTypes
fstar AlgebraTypes.fst --silent --cache_checked_modules 
echo Fraction Definition
fstar Fractions.Definition.fst --cache_checked_modules --silent
echo Fraction Equivalence
fstar Fractions.Equivalence.fst --cache_checked_modules --silent
echo Fraction Addition
fstar Fractions.Addition.fst --cache_checked_modules --silent
echo Fraction Multiplication
fstar Fractions.Multiplication.fst --cache_checked_modules --silent
echo Fraction Field
fstar Fractions.fst --cache_checked_modules --silent
echo FStar.IntegerIntervals
fstar FStar.IntegerIntervals.fst --cache_checked_modules --silent
echo FStar.Algebra.CommMonoid.Fold
fstar FStar.Algebra.CommMonoid.Fold.fst --cache_checked_modules --silent
echo FStar.Seq.Matrix
fstar FStar.Seq.Matrix.fst --cache_checked_modules --silent
echo FStar.Algebra.CommMonoid.Fold.Nested
fstar FStar.Algebra.CommMonoid.Fold.Nested.fst --cache_checked_modules --silent
echo Poly Definitions
fstar Polynomials.Definition.fst --cache_checked_modules --silent
echo Poly Equivalence
fstar Polynomials.Equivalence.fst --cache_checked_modules --silent
echo Poly Compact
fstar Polynomials.Compact.fst --cache_checked_modules --silent
echo Poly Addition
fstar Polynomials.Addition.fst --cache_checked_modules --silent
echo Poly Monomials
fstar Polynomials.Monomial.fst --cache_checked_modules --silent
echo Poly Multiplication
fstar Polynomials.Multiplication.fst --cache_checked_modules --silent
echo Poly Ring
fstar Polynomials.fst --cache_checked_modules --silent
echo RefinementEquality utility module
fstar RefinementEquality.fst --cache_checked_modules --silent
echo --- Recheck successful! ---
pause